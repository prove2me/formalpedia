-- Prove2me | Theorems.Thm_DetDLP_guarded_recovery_from_actual_packet_samples
-- name    : DetDLP.guarded_recovery_from_actual_packet_samples
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T16:43:46.678798+00:00
-- url     : https://prove2.me/theorems/3730ffb8-45f1-4dd9-8668-171f22fef04b
-- title:
--   Recovering the original contraction from the actual finite-ring packet samples
-- statement:
--   For an arbitrary placement of the original edges in occupied dyadic packet positions, the normalized Hermite and finite-grid interpolation weights recover the contraction to the original target precision. Each sample is the actual split-assignment sum using the represented Cauchy kernel at the indicated finite precision. The ambient integral subring may contain extension and truncated polynomial coefficients. For any lifts of the interpolated finite jets, the weighted reconstruction differs from the original contraction by 2^P times an element of that integral subring. The same weights work for all choices of tensors and terminal data. The finite quotient maps are assumed surjective with the specified precision kernel, and the finite grids have unit differences.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Sections 5.1–5.3, integral and finite-ring compatibility of the actual packet recurrence with guarded root recovery.

import Definitions.Def_DetDLP_OrientedPacketInstance

set_option autoImplicit false
open Finset Polynomial DetDLP.OrientedPacketInstance

namespace DetDLP

theorem guarded_recovery_from_actual_packet_samples {a N : ℕ} (G : BipartiteMultigraph) (active : Fin N→Finset (Pos a)) (L : Fin G.nE ≃ Address active)
    (P h u : ℕ) (hM : 0<G.nE) (lo : 3*G.nE≤h*u) (hi : h*u≤4*G.nE) :
    let Tm := univ.erase (0:ZMod (2^(a+1)))
    let v (t : ↥Tm) := padicValNat 2 t.val.val
    let m (t : ↥Tm) := h*(u-v t)
    let D (t : ↥Tm) := 2^(a-v t)
    let loss (t : ↥Tm) := 6*h*D t+4*G.nE*(a+1)
    let Q (t : ↥Tm) := P+8*h*D t+8*G.nE*(a+1)
    let n := G.nE*(2^(a+1)-1)+1
    ∃ w : ↥Tm→ℕ→ℚ, (∀ t j,w t j=0 ∨ -(loss t:ℤ)≤padicValRat 2 (w t j)) ∧
    ∀ (H : Type) [CommRing H] [Algebra ℚ H] (I : Subring H),
      (∀ q : ℚ,(q=0 ∨ 0≤padicValRat 2 q)→algebraMap ℚ H q∈I) →
    ∀ (R : ↥Tm→Type) [∀ t,CommRing (R t)] [∀ t,Algebra (ZMod (2^Q t)) (R t)]
      (π : (t : ↥Tm)→I→+*R t) (lift : (t : ↥Tm)→R t→I),
      (∀ t x,π t (lift t x)=x) → (∀ t x,π t x=0→(2:I)^Q t ∣ x) →
    ∀ (grid : (t : ↥Tm)→Fin n→R t), (∀ t i j,i≠j→IsUnit (grid t i-grid t j)) →
    ∃ V : (t : ↥Tm)→ℕ→Fin n→R t,∀ (T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→I)
      (U : (t : ↥Tm)→ZMod (2^(a+1))→(ZMod (2^Q t))[X]), (∀ t,Represents t.val (U t)) →
      let sample (t : ↥Tm) (j : Fin n) :=
        ∑ x : Fin G.nE→Bool,∑ y : Fin G.nE→Bool,
          DeformedContraction.weight (fun v z => π t (T v z)) x y *
            ∏ e,selector G active L (U t) (grid t j) x y e
      let jet (t : ↥Tm) (j : ℕ) := lift t (∑ k,V t j k*sample t k)
      ∃ E : I, (∑ t,∑ j∈range (m t),algebraMap ℚ H (w t j)*(jet t j:H))-
        BTNContract G (fun v z => (T v z:H))=(2:H)^P*(E:H) := by sorry
end DetDLP
