-- Prove2me | Theorems.Thm_BenignDegen_Supplement_theorem_6_3
-- name    : BenignDegen.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:31:48.842895+00:00
-- url     : https://prove2.me/theorems/eda8d741-e8e7-4f40-86e3-33cf44bbc392
-- title:
--   Theorem 6.3 — generic benign degeneracy: Theorem 4.3 holds at every order $d_\star(f)\le d\le n$ on an open dense semialgebraic null-complement set
-- statement:
--   Let $n\ge1$ and let $\mathcal P_n$ be the $2^n$-dimensional space of square-free polynomials on $\{\pm1\}^n$. For $f$ with a unique Boolean minimizer $x_\star$, the **first order of unique rank-one exactness** is
--   $$
--   d_\star(f)=\min\bigl\{1\le d\le n:\ \deg f\le 2d,\ \operatorname{argmin}(P_d)=\{b_d(x_\star)b_d(x_\star)^\top\}\bigr\}.
--   $$
--   There exists a set $\mathcal G_{\mathrm{gen}}\subseteq\mathcal P_n$ that is open, dense and semialgebraic, and whose complement has Lebesgue measure zero, such that every $f\in\mathcal G_{\mathrm{gen}}$ satisfies:
--
--   1. $f$ has a unique Boolean minimizer $x_\star$;
--   2. $d_\star(f)\le n$ is well defined (the set above is nonempty);
--   3. at every order $d_\star(f)\le d\le n$, the moment relaxation $(P_d)$ has the unique optimum $b_d(x_\star)b_d(x_\star)^\top$ and an optimal SOS certificate of rank $N_d-1$;
--   4. consequently, at every such order $d$, for every surjective equality encoding $\mathcal A$ of $(P_d)$ with feasible set $\{X:\mathcal AX=b\}=I_N+\mathcal T_d$ and cost $C=C_f$, the conclusions of Theorem 4.3 hold: for every $\sigma>0$ the canonical Douglas–Rachford residual satisfies the setwise error bound (3.9) around its fixed-point set $\mathcal Z_\star$ and its stall cone equals the tangent cone of $\mathcal Z_\star$ at every endpoint; for every $\sigma>0$ and $0<\tau<2$ every exact ADMM and exact sGS–ADMM run satisfies the conclusions of Corollary 5.1; and for every $\eta_x,\eta_y>0$ with $\eta_x\eta_y\|\mathcal A\|_{\mathrm{op}}^2<1$ every PDHG run satisfies the conclusions of Corollary 5.2.
--
--   So, outside a lower-dimensional semialgebraic set of objectives, the two hypotheses of Theorem 4.3 hold simultaneously at every uniquely rank-one exact order, and the three splitting methods converge eventually linearly from every initialization.
--
--   **Formalization Note** $\mathcal P_n$ is $\mathrm{Finset}(\mathrm{Fin}\,n)\to\mathbb R$ with the product topology and product Lebesgue measure; semialgebraicity is as in Theorem 6.2. $d_\star(f)$ is the infimum of the set of (2.5), asserted nonempty. Item 4 is stated with the same four conjuncts as the published goal `BenignDegen.theorem_4_3`, not assumed from it.
--
--   Differences from the source:
--   - generalization: the conclusions of Theorem 4.3 and Corollaries 5.1, 5.2 for the independent encoding (B.3) → the same conclusions for every surjective encoding A with {X : AX = b} = I_N + T_d and C = C_f; reason: as in the published goal BenignDegen.theorem_4_3; (B.3) is one such encoding (Proposition B.1), so the Lean statement specializes to the source's
--   - reading: G_gen ⊆ P_n (orders fixed with 1 ≤ d ≤ n, §2) → hypothesis 1 ≤ n; reason: the paper's standing order range 1 ≤ d ≤ n needs n ≥ 1; at n = 0 the set of (2.5) is empty and d⋆(f) is undefined
--   - reading: every fixed admissible parameter choice → σ > 0 (error bound, stall cone); σ > 0 and 0 < τ < 2 (ADMM, sGS–ADMM); η_x, η_y > 0 with η_xη_y‖A‖²_op < 1 (PDHG); reason: the parameter ranges of Theorem 4.3 and Corollaries 5.1, 5.2, exactly as in BenignDegen.theorem_4_3
--   - encoding: its complement has measure zero → volume Gᶜ = 0 for the product Lebesgue measure on Finset (Fin n) → ℝ; reason: Lebesgue measure in linear coordinates of P_n; null sets do not depend on the linear identification
--   - encoding: f has a unique Boolean minimizer x⋆ → ∃ x⋆, ∀ x ∈ {±1}ⁿ, f(x) = OPT(f) ↔ x = x⋆; reason: same condition
--   - encoding: d⋆(f) ≤ n is well defined; at every order d⋆(f) ≤ d ≤ n → the set {1 ≤ d ≤ n : deg f ≤ 2d, UniqueRankOneOpt n d f x⋆} of (2.5) is nonempty, d⋆(f) is its sInf, and the conclusions hold for every d with d⋆(f) ≤ d ≤ n; reason: (2.5) defines d⋆(f) as the minimum of that set; nonemptiness is what makes it well defined, and it is then ≤ n
--   - encoding: an optimal certificate of rank N_d − 1 → HasSCCertificate n d f (some S ∈ S⋆ of (2.4) with f⋆ = OPT(f) and rank S = N_d − 1); reason: published base definition; same condition
--   - encoding: square-free objectives, open, dense, semialgebraic in P_n → coefficient functions Finset (Fin n) → ℝ, IsOpen, Dense (product topology), IsSemialgebraicCoeff; reason: linear coordinates of P_n and BCR's semialgebraic sets, as in Theorem 6.2
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, §6, Theorem 6.3, p.12 (proof §6 and Appendix G.3, p.32)

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
import Definitions.Def_NonconvexSplitting_ADMMKL_Semialgebraic
import Definitions.Def_BenignDegen_Supplement_Semialgebraic
import Definitions.Def_BenignDegen_Supplement_Cells
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

namespace Supplement

/-- Theorem 6.3 (generic benign degeneracy), Kang, *Benign Degeneracy for First-Order Methods in
Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.12 (proof §6 and Appendix G.3).
There is an open dense semialgebraic set `G_gen ⊆ P_n`, whose complement has Lebesgue measure
zero, such that every `f ∈ G_gen` has a unique Boolean minimizer `x⋆`, `d⋆(f) ≤ n` is well
defined (the set of (2.5) is nonempty), and at every order `d⋆(f) ≤ d ≤ n` the moment relaxation
has the unique optimum `b_d(x⋆)b_d(x⋆)^⊤` and an optimal certificate of rank `N_d − 1`.
Consequently, for every such `f` and `d`, every surjective encoding with feasible set
`I_N + T_d` and cost `C_f`, and every admissible parameter choice, the conclusions of Theorem 4.3
and Corollaries 5.1 and 5.2 hold (the four conjuncts of `BenignDegen.theorem_4_3`).

**Formalization Note** `P_n` is `Finset (Fin n) → ℝ` with the product topology and the product
Lebesgue measure `volume`. The encoding is any surjective `A` with `{X : AX = b} = I_N + T_d`
and `C = C_f`, as in `BenignDegen.theorem_4_3`; the independent encoding (B.3) is one such
(Proposition B.1). Standing assumption: `n ≥ 1` (orders satisfy `1 ≤ d ≤ n`). -/
theorem theorem_6_3 (n : ℕ) (hn : 1 ≤ n) :
    ∃ G : Set (Finset (Fin n) → ℝ),
      IsOpen G ∧ Dense G ∧ IsSemialgebraicCoeff G ∧ MeasureTheory.volume Gᶜ = 0 ∧
      ∀ f ∈ G, ∃ xs : Fin n → ℤˣ, (∀ x : Fin n → ℤˣ, evalPoly f x = cubeMin f ↔ x = xs) ∧
        (dStarSet n f xs).Nonempty ∧
        ∀ d : ℕ, dStar n f xs ≤ d → d ≤ n →
          UniqueRankOneOpt n d f xs ∧ HasSCCertificate n d f ∧
          ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (D : SDPData (Idx n d) κ),
            Function.Surjective D.A → IsBoolEncoding D → D.C = Cf n d f →
            (∀ σ : ℝ, 0 < σ → D.ErrorBound σ) ∧
            (∀ σ : ℝ, 0 < σ → ∀ Zbar ∈ D.Zstar σ,
              D.stallCone σ Zbar = SunNLSDP.Equiv.tangentCone (D.Zstar σ) Zbar) ∧
            (∀ σ : ℝ, 0 < σ → ∀ τ : ℝ, 0 < τ → τ < 2 →
              (∀ (X S : ℕ → SymMat (Idx n d)) (lam : ℕ → EuclideanSpace ℝ κ),
                D.IsADMMRun σ τ X S lam → D.ADMMConclusions σ τ X S lam) ∧
              (∀ (X S : ℕ → SymMat (Idx n d)) (lamH lam : ℕ → EuclideanSpace ℝ κ),
                D.IsSGSRun σ τ X S lamH lam → D.ADMMConclusions σ τ X S lam)) ∧
            (∀ ηx ηy : ℝ, 0 < ηx → 0 < ηy → ηx * ηy * ‖D.A‖ ^ 2 < 1 →
              ∀ (X : ℕ → SymMat (Idx n d)) (lam : ℕ → EuclideanSpace ℝ κ),
                D.IsPDHGRun ηx ηy X lam → D.PDHGConclusions ηx ηy X lam) := by sorry

end Supplement

end BenignDegen
