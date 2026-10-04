-- Prove2me | Theorems.Thm_BalcanDDA_Piecewise_theorem3_3_pdim_bound
-- name    : BalcanDDA.Piecewise.theorem3_3_pdim_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:17:30.641611+00:00
-- url     : https://prove2.me/theorems/3552a196-b05b-46d2-9c0b-29796a359092
-- title:
--   Theorem 3.3 — pseudo-dimension bound from a piecewise-decomposable dual class (explicit form)
-- statement:
--   Let $\mathcal X$ be a set of problem instances and $\mathcal U \subseteq \mathbb R^{\mathcal X}$ a class of utility functions. Suppose that the dual class $\mathcal U^*$ is $(\mathcal F, \mathcal G, k)$-piecewise decomposable with boundary functions $\mathcal G \subseteq \{0,1\}^{\mathcal U}$ and piece functions $\mathcal F \subseteq \mathbb R^{\mathcal U}$, where $k \ge 1$. Let $d_F = \mathrm{Pdim}(\mathcal F^*)$, $d_G = \mathrm{VCdim}(\mathcal G^*)$ and $D = d_F + d_G$. Put
--   $$a = \frac{D}{\ln 2}, \qquad b = \frac{D + d_G \ln k}{\ln 2}.$$
--   Then every tuple $x_1, \dots, x_N$ of problem instances shattered by $\mathcal U$ satisfies
--   $$N \le 4a\ln(2a) + 2b,$$
--   so $\mathrm{Pdim}(\mathcal U) \le 4a\ln(2a) + 2b$. This is the explicit bound behind the paper's
--   $$\mathrm{Pdim}(\mathcal U) = O\bigl((\mathrm{Pdim}(\mathcal F^*) + \mathrm{VCdim}(\mathcal G^*)) \ln(\mathrm{Pdim}(\mathcal F^*) + \mathrm{VCdim}(\mathcal G^*)) + \mathrm{VCdim}(\mathcal G^*) \ln k\bigr).$$
--
--   This is the paper's main general theorem: whenever the performance of a parameterized algorithm on each fixed instance is piecewise structured as a function of the algorithm, the sample complexity of tuning its parameters is controlled by the complexity of the boundary and piece functions and the number $k$ of boundaries. It is instantiated for clustering, integer programming, greedy algorithms, sequence alignment and mechanism design.
--
--   **Formalization Note.** The $O(\cdot)$ is replaced by the explicit bound the paper's proof yields: its last step bounds $\mathrm{Pdim}(\mathcal U)$ by the largest $N$ with $2^N \le (ekN)^{d_G}(eN)^{d_F}$, and taking logarithms and applying Lemma A.1 gives the constants above. Pseudo-dimension and VC-dimension are the published exact-value predicates `PseudoDim` and `HasVCDim` (so $d_F$, $d_G$ are finite, as the paper's bound presupposes); "$\mathrm{Pdim}(\mathcal U) \le B$" is stated as "every shattered tuple has length at most $B$". Shattering uses strict thresholds $u(x_i) > z_i$; the paper leaves $\mathrm{sign}(0)$ unspecified, and the strict and non-strict versions shatter exactly the same tuples (finitely many witnesses allow shifting each threshold), so the pseudo-dimension is unchanged. Added hypothesis: $k \ge 1$ (correction: $\ln k$ is undefined at $k = 0$ and Lean's $\ln 0 = 0$ would change the bound). The case $D = 0$ is included: there $a = b = 0$, the bound reads $N \le 0$, and indeed $2^N \le 1$ forces $\mathrm{Pdim}(\mathcal U) = 0$, the paper's $O(0)$; Lemma A.1 (which needs $a \ge 1$) is only used when $D \ge 1$. The paper's range $[0, H]$ of the utility functions is dropped, since neither the theorem nor its proof uses it; the statement is therefore slightly more general. Parameters $\rho$ are indexed by the functions $u_\rho \in \mathcal U$ themselves, since the theorem depends on $\mathcal U$ only as a set of functions.
-- source:
--   Balcan et al., How Much Data Is Sufficient to Learn High-Performing Algorithms?, arXiv:1908.02894v4, p. 8, Theorem 3.3 (explicit bound from its proof, p. 9, and Lemma A.1, p. 50)

import Mathlib
import Definitions.Def_FoundationsML_Regression_Shatters
import Definitions.Def_FoundationsML_Regression_PseudoDim
import Definitions.Def_FoundationsML_RademacherVC_GrowthFunction
import Definitions.Def_FoundationsML_RademacherVC_HasVCDim
import Definitions.Def_BalcanDDA_Piecewise_dual
import Definitions.Def_BalcanDDA_Piecewise_PiecewiseDecomposable

open FoundationsML.Regression FoundationsML.RademacherVC

namespace BalcanDDA.Piecewise

/-- Theorem 3.3 (Balcan et al., arXiv:1908.02894v4, p. 8), in the explicit form its proof
(p. 9) yields. Suppose the dual class `U*` is `(F, G, k)`-piecewise decomposable with
boundary functions `G ⊆ {0,1}^U` and piece functions `F ⊆ ℝ^U`, with `Pdim(F*) = dF`,
`VCdim(G*) = dG` and `k ≥ 1`; write `D = dF + dG`. Then every tuple `x₁, …, x_N` shattered by
`U` has `N ≤ 4a ln(2a) + 2b`, where `a = D / ln 2` and `b = (D + dG ln k) / ln 2`; i.e.
`Pdim(U) ≤ 4a ln(2a) + 2b = O(D ln D + dG ln k)`. At `D = 0` the bound is `0`, which is the
paper's `O(0)`: then `2^N ≤ 1` forces `N = 0`. -/
theorem theorem3_3_pdim_bound {X : Type*} (U : Set (X → ℝ)) (F : Set (↥U → ℝ))
    (G : Set (↥U → Bool)) (k dF dG : ℕ)
    (hk : 1 ≤ k)
    (hdec : PiecewiseDecomposable (dual U) F G k)
    (hF : PseudoDim (dual F) dF) (hG : HasVCDim (dualB G) dG) :
    ∀ (N : ℕ) (x : Fin N → X), Shatters U x →
      (N : ℝ) ≤ 4 * (((dF + dG : ℕ) : ℝ) / Real.log 2) *
          Real.log (2 * (((dF + dG : ℕ) : ℝ) / Real.log 2)) +
        2 * ((((dF + dG : ℕ) : ℝ) + (dG : ℝ) * Real.log k) / Real.log 2) := by sorry

end BalcanDDA.Piecewise
