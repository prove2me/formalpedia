-- Prove2me | Theorems.Thm_BorderD4_theorem_6_7
-- name    : BorderD4.theorem_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:01:54.135913+00:00
-- url     : https://prove2.me/theorems/6a1fa000-7da4-47db-ae31-0de8cf019a28
-- title:
--   Theorem 6.7: border low-weight translation
-- statement:
--   Let $F$ be algebraically closed of characteristic zero, and $f\in F[x]$ with $f+\varepsilon S=\sum_{i=1}^k T_i$, where $S\in F[[\varepsilon]][x]$ and $T_i=\prod_j q_{i,j}$ for $q_{i,j}\in F((\varepsilon))[x]$ of degree at most $\delta$, at most $\rho\ge 1$ of them distinct. Then there exist $T\subseteq[N]$ with $N-|T|\le k$ and $b\in F^N$ with $|\mathrm{supp}(b)|=O(k^2\Delta^3)$, $\Delta=\delta^k$, $u=x_T$, such that:
--
--   1. for each $a\notin T$ there are $\varphi_a\in F[[\varepsilon,u]]$ and $Q_a\in F[[\varepsilon]][u,x_a]$ of degree at most $\Delta$ with $\varphi_a(\varepsilon,0)=0$, $Q_a(u,\varphi_a)=0$, and $(\partial_{x_a}Q_a)(u,\varphi_a)$ an $\varepsilon$-unit;
--   2. there are $0\le k'\le k$, integers $e_i$ and $p_{i,j}\in F[[\varepsilon]][x]$ of degree at most $\delta$, at most $\rho$ distinct, with every $p_{i,j}(u,\varphi)$ an $\varepsilon$-unit and
--   $$\sum_{i=1}^{k'}\varepsilon^{e_i}\prod_j p_{i,j}(u,\varphi)\equiv f(b+(u,\varphi))\pmod\varepsilon.$$
--
--   The constant in the $O$ is absolute. The theorem holds for every polynomial with such a representation, and is the input to the differentiation argument of §6.3.
--
--   Differences from the source:
--   - generalization: §6 fixes $N=(k+1)n$ (p.49) → an arbitrary finite nonempty index type; reason: the proof uses $N$ only as the number of variables; $\mathrm{Fin}(k+1)\times\mathrm{Fin}\,n$ is the source
--   - encoding: the congruence (20) in $F[[\varepsilon,u]]_\varepsilon$ → an equation in the fraction field of $F[[\varepsilon,u]]$ with witness $S_0\in F[[\varepsilon,u]]$; reason: the paragraph after (20) says this; the localization embeds in the fraction field
--   - encoding: the form of the circuit → $f+\varepsilon S=\sum_{i:\mathrm{Fin}\,k}\prod$ over a list of factors; reason: a gate may be $0$, so this covers top fan-in at most $k$
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 6.7, p.52

import Mathlib
import Definitions.Def_BorderD4_BorderComputes
import Definitions.Def_BorderD4_LowWeightForm
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries
universe u v

namespace BorderD4

open Classical in
/-- Theorem 6.7, border low-weight translation: if `f + εS = ∑_{i=1}^k T_i`, with `S ∈ F[[ε]][x]` and `T_i = ∏_j q_{i,j}` for
`q_{i,j} ∈ F((ε))[x]` of degree at most `δ`, at most `ρ ≥ 1` of them distinct, then `f` has the low-weight form
`LowWeightForm`, with a point `b` satisfying `|supp(b)| = O(k² Δ³)`, `Δ = δ^k`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 6.7, p.52.

**Formalization Note** The `O` hides an absolute constant, chosen before `F`, `σ`, `k`, `δ` (the proof gives
`(C + 1) · Δ · CΔ²`, p.58). The gates are indexed by `Fin k`, so a gate may be zero. -/
theorem theorem_6_7 : ∃ A : ℕ, ∀ {F : Type u} [Field F] [IsAlgClosed F] [CharZero F]
    {σ : Type v} [Fintype σ] [DecidableEq σ] [Nonempty σ] {k δ ρ : ℕ}, 1 ≤ k → 1 ≤ δ → 1 ≤ ρ →
    ∀ (f : MvPolynomial σ F) (S : MvPolynomial σ F⟦X⟧)
      (q : Fin k → List (MvPolynomial σ (LaurentSeries F))),
      (∀ i, ∀ x ∈ q i, x.totalDegree ≤ δ) →
      (Finset.univ.biUnion fun i => (q i).toFinset).card ≤ ρ →
      map (algebraMap F (LaurentSeries F)) f
          + MvPolynomial.C (epsK F) * map (algebraMap F⟦X⟧ (LaurentSeries F)) S =
        ∑ i, (q i).prod →
      ∃ D : LowWeightForm f k δ ρ, (Function.support D.b).ncard ≤ A * k ^ 2 * (δ ^ k) ^ 3 := by sorry

end BorderD4
