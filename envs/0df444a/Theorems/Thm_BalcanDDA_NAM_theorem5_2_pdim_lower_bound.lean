-- Prove2me | Theorems.Thm_BalcanDDA_NAM_theorem5_2_pdim_lower_bound
-- name    : BalcanDDA.NAM.theorem5_2_pdim_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T06:37:28.174006+00:00
-- url     : https://prove2.me/theorems/d05b3da6-f862-42f4-b5cd-e05ac1a61582
-- title:
--   Theorem 5.2 (corrected) — neutral affine maximizers: $\mathrm{Pdim}(\mathcal U) \ge \lfloor n/2 \rfloor$
-- statement:
--   Consider $n\ge1$ agents and $m\ge2$ alternatives, and let $\mathcal U=\{u_\rho \mid \rho\in\mathbb R^n_{\ge0},\ \{i\mid\rho[i]=0\}\ne\emptyset\}$ be the class of social-welfare utilities $u_\rho(v)=\sum_{i=1}^n v_i(\psi_\rho(v))$ of neutral affine maximizers, where $\psi_\rho(v)$ is a maximizer over $j\in[m]$ of $\sum_{i}\rho[i]v_i(j)$, chosen by an arbitrary but fixed tie-breaking rule. Then
--   $$\mathrm{Pdim}(\mathcal U)\ \ge\ \Bigl\lfloor \frac n2\Bigr\rfloor ,$$
--   i.e. there are $\lfloor n/2\rfloor$ valuation profiles $v^{(1)},\dots,v^{(\lfloor n/2\rfloor)}\in\mathbb R^{nm}$ and witnesses $z^{(1)},\dots,z^{(\lfloor n/2\rfloor)}\in\mathbb R$ such that for every $b\in\{0,1\}^{\lfloor n/2\rfloor}$ some $u_\rho\in\mathcal U$ satisfies $u_\rho(v^{(\ell)})>z^{(\ell)}$ exactly when $b_\ell=1$.
--
--   Combined with the upper bound $\mathrm{Pdim}(\mathcal U)=O(n\ln m)$ that the paper derives from its Theorem 3.3 and Lemma 5.1, this shows that the general pseudo-dimension bound is tight up to logarithmic factors.
--
--   Corrections relative to the printed statement (p. 23):
--   1. The paper states $\mathrm{Pdim}(\mathcal U)\ge n/2$; its proof assumes $n$ even "without loss of generality" and shatters $n/2$ profiles. The printed bound fails at $n=1$: the only admissible parameter is $\rho=0$, so $\mathcal U$ consists of a single function and $\mathrm{Pdim}(\mathcal U)=0<\tfrac12$. The statement here is $\lfloor n/2\rfloor$, which equals $n/2$ for even $n$.
--   2. The printed set-builder reads "$\{\rho[i]\mid i=0\}\neq\emptyset$"; Lemma 5.1 one paragraph earlier writes $\{i\mid\rho[i]=0\}\neq\emptyset$ (some agent has weight zero), which is the condition used here.
--   3. The hypotheses $n\ge1$ and $m\ge2$ are explicit: for $n=0$ no parameter is admissible and $\mathcal U=\emptyset$; for $m=1$, $\mathcal U$ is a single function. The paper's proof takes $m=2$; the theorem is stated for every $m\ge2$.
--
--   **Formalization Note** "$\mathrm{Pdim}(\mathcal U)\ge N$" is written as the existence of an $N$-tuple of profiles shattered by `namClass ψ` in the sense of `FoundationsML.Regression.Shatters`, which uses the strict threshold `t i < g (z i)`. The paper leaves $\mathrm{sign}(0)$ unspecified; since a shattering is witnessed by finitely many functions, the strict and non-strict readings shatter the same tuples. `n / 2` is natural-number division, $\lfloor n/2\rfloor$. The theorem holds for every outcome rule `ψ` satisfying `IsArgmaxSelector ψ`, i.e. for every tie-breaking rule.
-- source:
--   Balcan et al., How Much Data Is Sufficient to Learn High-Performing Algorithms?, arXiv:1908.02894v4, p. 23, Theorem 5.2 (proof pp. 23–24); pseudo-dimension p. 6, eq. (1)

import Mathlib
import Definitions.Def_FoundationsML_Regression_Shatters
import Definitions.Def_BalcanDDA_NAM_Model

namespace BalcanDDA.NAM

/-- Theorem 5.2 (Balcan et al., arXiv:1908.02894v4, p. 23), corrected to `⌊n/2⌋`: for
`n ≥ 1` agents, `m ≥ 2` alternatives and every argmax outcome rule `ψ`, the class of NAM
welfare functions pseudo-shatters some `⌊n/2⌋` valuation profiles, i.e.
`Pdim(U) ≥ ⌊n/2⌋`. -/
theorem theorem5_2_pdim_lower_bound (n m : ℕ) (hn : 1 ≤ n) (hm : 2 ≤ m)
    (ψ : (Fin n → ℝ) → (Fin n → Fin m → ℝ) → Fin m) (hψ : IsArgmaxSelector ψ) :
    ∃ v : Fin (n / 2) → (Fin n → Fin m → ℝ),
      FoundationsML.Regression.Shatters (namClass ψ) v := by sorry

end BalcanDDA.NAM
