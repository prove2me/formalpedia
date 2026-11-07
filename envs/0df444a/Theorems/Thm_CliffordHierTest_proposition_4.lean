-- Prove2me | Theorems.Thm_CliffordHierTest_proposition_4
-- name    : CliffordHierTest.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:01.416859+00:00
-- url     : https://prove2.me/theorems/b81fc6a5-e490-4b14-8284-c76042284bb1
-- title:
--   Proposition 4 — Weyl multiplication and commutation relations
-- statement:
--   Let $d$ be prime and $n\ge0$. There is a map $\beta:\mathbb F_d^{2n}\times\mathbb F_d^{2n}\to\mathbb Z_D$ such that for all $a,b\in\mathbb F_d^{2n}$
--   $$W_aW_b=\tau^{\beta(a,b)}W_{a+b},\qquad W_aW_b=\omega^{[a,b]}W_bW_a,$$
--   where $[(u,v),(u',v')]=u\cdot v'-u'\cdot v$ is the standard symplectic form.
--
--   These relations make the Weyl operators a projective representation of $\mathbb F_d^{2n}$ and underlie every later computation with the Pauli group.
--
--   **Formalization Note** $\tau^{\beta(a,b)}$ and $\omega^{[a,b]}$ are powers by the natural-number representatives of $\beta(a,b)\in$ `ZMod (phaseModulus d)` and $[a,b]\in$ `ZMod d`.
--
--   Differences from the source:
--
--   - encoding: τ^{β(a,b)}, ω^{[a,b]} with exponents in ℤ_D, 𝔽_d → powers by the natural-number representatives (.val); reason: τ has order D and ω order d, so the power does not depend on the representative
-- source:
--   Bao, Briët, Castro-Silva, van Dordrecht, Helsen, On Clifford hierarchy testing and near-extremizers of noncommutative uniformity norms, arXiv:2605.26983 (held version, sha256 610d53a6…), §2.1 Proposition 4, p.4

import Mathlib
import Definitions.Def_CliffordHierTest_PauliNorm

open scoped Matrix

namespace CliffordHierTest

open QAlgorithms.Papers.Independent.Extend50.P30

/-- **Proposition 4** (p.4). Z. Bao, J. Briët, D. Castro-Silva, P. van Dordrecht, J. Helsen, *On Clifford hierarchy testing and
near-extremizers of noncommutative uniformity norms*, arXiv:2605.26983 (held version, sha256 610d53a6…).
There is a map `β : 𝔽_d^{2n} × 𝔽_d^{2n} → ℤ_D` with `W_a W_b = τ^{β(a,b)} W_{a+b}` and
`W_a W_b = ω^{[a,b]} W_b W_a` for all `a, b`.

**Formalization Note.** `d` prime (standing assumption of §2.1). `ℤ_D` is `ZMod (phaseModulus d)`
and `τ^{β(a,b)}` is `weylPhase d ^ (β a b).val`; `ω^{[a,b]}` is `weylRoot d ^ [a,b].val` (both
`τ` and `ω` have the matching orders `D` and `d`). `W_a = cyclicWeyl d n a`, `[a, b] =
symplecticBracket a b = u·v′ − u′·v`. -/
theorem proposition_4 (d n : ℕ) [Fact (Nat.Prime d)] :
    ∃ β : DiscretePhaseSpace d n → DiscretePhaseSpace d n → ZMod (phaseModulus d),
      ∀ a b : DiscretePhaseSpace d n,
        cyclicWeyl d n a * cyclicWeyl d n b = weylPhase d ^ (β a b).val • cyclicWeyl d n (a + b) ∧
        cyclicWeyl d n a * cyclicWeyl d n b =
          weylRoot d ^ (symplecticBracket a b).val • (cyclicWeyl d n b * cyclicWeyl d n a) := by sorry

end CliffordHierTest
