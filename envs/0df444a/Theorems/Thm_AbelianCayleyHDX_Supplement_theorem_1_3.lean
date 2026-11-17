-- Prove2me | Theorems.Thm_AbelianCayleyHDX_Supplement_theorem_1_3
-- name    : AbelianCayleyHDX.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:06:10.684736+00:00
-- url     : https://prove2.me/theorems/1824bca2-8ddb-4a8e-9642-389dafa1fd41
-- title:
--   Theorem 1.3 — explicit weighted $d$-dimensional Cayley complexes over $\mathbb F_2^n$ with codimension-two link norm $\le 1/d$ and Cayley degree $\Theta_d(n)$
-- statement:
--   For every fixed $d\ge 2$ there is an explicit infinite family of weighted $d$-dimensional Cayley complexes over $\mathbb F_2^n$, with $n\to\infty$ along the family. Each complex is simple, pure and translation invariant, and its top-face probability distribution has full support. Its one-skeleton and all positive-dimensional links are connected. On every codimension-two link, the random-walk operator has norm at most $1/d$ on the orthogonal complement of the constants in $L^2$ of the stationary measure. The Cayley degree is $\Theta_d(n)$.
--
--   Precisely: for every $d\ge2$ there are constants $c_d,C_d>0$ and a sequence $(n_j,S_j,X_j(d),\mu_j)_{j\in\mathbb N}$ with $n_j\to\infty$ such that, for every $j$,
--
--   1. $(X_j,\mu_j)$ is a weighted $d$-dimensional Cayley complex over $\mathbb F_2^{n_j}$ with generators $S_j$ ($\mu_j$ a probability distribution with full support on the $(d+1)$-element top faces, one-skeleton $\mathrm{Cay}(\mathbb F_2^{n_j},S_j)$, edge weights depending only on the generator) and it is translation invariant;
--   2. $\mathrm{Cay}(\mathbb F_2^{n_j},S_j)$ is connected, and the link of every face with at most $d-1$ vertices is connected;
--   3. for every face $\sigma$ with $d-1$ vertices the weighted link graph of $\sigma$ is a two-sided $1/d$-spectral expander:
--   $$\big\|P_\sigma|_{\mathbf 1^{\perp\pi_\sigma}}\big\|_{\pi_\sigma}\le\frac1d;$$
--   4. $c_d\,n_j\le|S_j|\le C_d\,n_j$;
--
--   and the family is explicit (one algorithm printing $n_j$, the generators, the orbit representatives and their exact rational weights in time polynomial in $n_j$).
--
--   The degree is optimal in order, and the result answers the question of Dikstein, Liu and Wigderson at the endpoint $\lambda=1/d$ in every dimension.
--
--   **Formalization Note** $c_d$ and $C_d$ are chosen after $d$ and before the family; the bounds hold for every member. Simple and pure hold by the encoding. The empty face is included in the link clause; its link is the whole complex.
--
--   Differences from the source:
--   - encoding: $\mathbb F_2^n$, a complex with full-support top-face probability distribution → `Vec n` (`Fin n → ZMod 2`), a `Finset` of $(d+1)$-element top faces with a rational weight function; reason: Lean convention; the weights of an explicit family are exact rationals, so the instances are the same.
--   - encoding: $\Theta_d(n)$ → $\exists\,c_d,C_d>0$ with $c_d n_j\le|S_j|\le C_d n_j$ for every $j$; reason: the standard meaning of $\Theta_d$ with constants depending on $d$ only; "for every $j$" is equivalent to "for all large $j$" here, since $|S_j|\ge1$ and $n_j\ge1$ for every member, so finitely many exceptions are absorbed into $c_d,C_d$.
--   - encoding: induced edge weights $\mu_1(\{x,x+s\})$ depending only on $s$ → equality of the unnormalized masses $\sum_{\tau\supseteq\{x,x+s\}}\mu(\tau)$; reason: $\mu_1$ is this mass times the constant $\binom{d+1}{2}^{-1}$.
--   - encoding: link random walk with conditioned induced weights → unnormalized link weights $\sum_{\tau\supseteq\sigma\cup\{u,v\}}\mu(\tau)$; reason: a common positive factor changes neither the walk nor its stationary measure.
--   - encoding: "explicit" (Section 2.3) → one Turing machine and one polynomial with output in fixed binary encodings within $p(n_j)$ steps; reason: same reading as the base mission's explicitness clause.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Theorem 1.3, p.4 (proof Section 5, pp.19–21; definitions Sections 2.2–2.3, pp.8–9)

import Mathlib
import Definitions.Def_ReplParity_Vec
import Definitions.Def_AbelianCayleyHDX_cayleyGraph
import Definitions.Def_AbelianCayleyHDX_Supplement_IsWeightedCayleyComplex
import Definitions.Def_AbelianCayleyHDX_Supplement_IsWeightedTranslationInvariant
import Definitions.Def_AbelianCayleyHDX_Supplement_IsFace
import Definitions.Def_AbelianCayleyHDX_Supplement_LinkConnected
import Definitions.Def_AbelianCayleyHDX_Supplement_HasCodimTwoLocalSpectralNorm
import Definitions.Def_AbelianCayleyHDX_Supplement_IsExplicitWeightedFamily
open Filter
open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement

/-- **Theorem 1.3** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Theorem 1.3, p.4; proof Section 5, pp.19–21). "For every fixed
`d ≥ 2`, there is an explicit infinite family of weighted `d`-dimensional Cayley complexes over
`𝔽₂ⁿ`, with `n → ∞` along the family. Each complex is simple, pure, and translation invariant, and
its top-face probability distribution has full support. Its one-skeleton and all
positive-dimensional links are connected. On every codimension-two link, the random-walk operator
has norm at most `1/d` on the orthogonal complement of the constants in `L²` of the stationary
measure. The Cayley degree is `Θ_d(n)`."

Stated as: for every `d ≥ 2` there are constants `c_d, C_d > 0` and a sequence
`(n_j, S_j, tops_j, μ_j)` with `n_j → ∞` such that for every `j`:
`(tops_j, μ_j)` is a weighted `d`-dimensional Cayley complex over `𝔽₂^{n_j}` with generators `S_j`
(full support, probability weights), translation invariant; `Cay(𝔽₂^{n_j}, S_j)` is connected;
the link of every face with at most `d − 1` vertices (every face of dimension `≤ d − 2`, i.e. every
link of positive dimension) is connected; every codimension-two link is a two-sided
`1/d`-spectral expander; and `c_d n_j ≤ |S_j| ≤ C_d n_j`; and the family is explicit
(Section 2.3, p.9).

**Formalization Note** `c_d, C_d` are chosen after `d` and before the family, so they depend on
`d` only (`Θ_d`); the degree bounds hold for every member, not only eventually. Simple and pure hold
by the encoding (a `Finset` of `(d+1)`-element top faces). The face `σ = ∅` is included in the link
clause (its link is the whole complex, whose one-skeleton is `Cay(𝔽₂^{n_j}, S_j)`). -/
theorem theorem_1_3 :
    ∀ d : ℕ, 2 ≤ d → ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∃ (n : ℕ → ℕ) (S : ∀ j, Finset (Vec (n j))) (tops : ∀ j, Finset (Finset (Vec (n j))))
        (μ : ∀ j, Finset (Vec (n j)) → ℚ),
        Tendsto n atTop atTop ∧
        (∀ j, IsWeightedCayleyComplex d (S j) (tops j) (μ j) ∧
          IsWeightedTranslationInvariant (tops j) (μ j) ∧
          (AbelianCayleyHDX.cayleyGraph (S j)).Connected ∧
          (∀ σ : Finset (Vec (n j)), IsFace (tops j) σ → σ.card ≤ d - 1 →
            LinkConnected (tops j) σ) ∧
          HasCodimTwoLocalSpectralNorm d (tops j) (μ j) (1 / (d : ℝ)) ∧
          c * (n j : ℝ) ≤ ((S j).card : ℝ) ∧ ((S j).card : ℝ) ≤ C * (n j : ℝ)) ∧
        IsExplicitWeightedFamily n S tops μ := by sorry

end AbelianCayleyHDX.Supplement
