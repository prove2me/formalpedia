-- Prove2me | Theorems.Thm_F3SubsetSum_corollary_4_18
-- name    : F3SubsetSum.corollary_4_18
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T12:31:00.078835+00:00
-- url     : https://prove2.me/theorems/78db0d16-a0c3-40b6-82cf-5e3a06e3e10e
-- title:
--   Corollary 4.18 — reduction of $\bar\rho(W)$ to shadows of monomial families
-- statement:
--   Let $q\ge3$ be prime, $D\ge2$, $c=\min\{q-1,D\}$, and $W\subseteq\overline R{}_D^*$ a nonzero subspace. There are families $\mathcal A_d$, $0\le d\le c$, of reduced degree-$(D-d)$ monomials such that
--
--   1. $\dim W=\sum_{d=0}^c|\mathcal A_d|$;
--   2. $\bar\rho(W)\ge\sum_{d=2}^c|\mathcal A_d|$;
--   3. $\partial\mathcal A_d\subseteq\mathcal A_{d+1}$ for every $0\le d\le c-1$.
--
--   The families come from splitting a $\mathcal B$-fixed monomial family (Lemma 4.17) by the exponent of $x_1$; the shadow condition is what Theorem 4.19 turns into a size bound.
--
--   Differences from the source:
--   - encoding: the standing integer D ≥ 2 of §4.1 (eq. (29), p.18), left implicit in the statement → hypothesis D ≥ 2; reason: R*_{D−2} is undefined for D < 2 (natural-number subtraction would make it R*_0)
--   - encoding: families 𝒜_d, 0 ≤ d ≤ c → a family 𝒜 d for every d ∈ ℕ, constrained and used only for d ≤ c; reason: families with d > c play no role
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Corollary 4.18, p.27 (proof pp.27–28)

import Mathlib
import Definitions.Def_F3SubsetSum_TruncatedRing
import Definitions.Def_F3SubsetSum_SymbolicRank
import Definitions.Def_F3SubsetSum_MonomialShadow

namespace F3SubsetSum

/-- **Corollary 4.18** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1,
Corollary 4.18, p.27; proof pp.27–28): "Define c = min{q − 1, D}. For every nonzero subspace
W ⊆ R̄*_D, there are families 𝒜_d, 0 ≤ d ≤ c of reduced degree-(D − d) monomials such that
1. dim(W) = Σ_{d=0}^c |𝒜_d|,
2. ρ̄(W) ≥ Σ_{d=2}^c |𝒜_d|,
3. ∂𝒜_d ⊆ 𝒜_{d+1} holds for every 0 ≤ d ≤ c − 1."

Over the algebraic closure `F̄_q`, `q ≥ 3` prime, `D ≥ 2` (the standing range of `D`, p.18).
Monomials are exponent vectors; a monomial is reduced when every exponent is below `q`, and its
degree is `monoDeg`. The shadow `∂` is that of p.27.

**Formalization Note** The families are indexed by all `d : ℕ`; only `0 ≤ d ≤ c` is
constrained or used. -/
theorem corollary_4_18 (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (n D : ℕ) (hD : 2 ≤ D)
    (W : Submodule (AlgebraicClosure (ZMod q))
      (Module.Dual (AlgebraicClosure (ZMod q)) (Rd (AlgebraicClosure (ZMod q)) n q D)))
    (hW : W ≠ ⊥) :
    ∃ 𝒜 : ℕ → Finset (Fin n →₀ ℕ),
      (∀ d ≤ min (q - 1) D, ∀ α ∈ 𝒜 d, (∀ j, α j < q) ∧ monoDeg α = D - d) ∧
      Module.finrank (AlgebraicClosure (ZMod q)) W =
        ∑ d ∈ Finset.range (min (q - 1) D + 1), (𝒜 d).card ∧
      ∑ d ∈ Finset.Icc 2 (min (q - 1) D), (𝒜 d).card ≤
        symbolicRank (AlgebraicClosure (ZMod q)) n q D W ∧
      ∀ d < min (q - 1) D, shadow (𝒜 d) ⊆ 𝒜 (d + 1) := by sorry

end F3SubsetSum
