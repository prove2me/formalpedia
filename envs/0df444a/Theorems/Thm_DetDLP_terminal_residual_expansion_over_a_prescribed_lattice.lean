-- Prove2me | Theorems.Thm_DetDLP_terminal_residual_expansion_over_a_prescribed_lattice
-- name    : DetDLP.terminal_residual_expansion_over_a_prescribed_lattice
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T19:17:42.91694+00:00
-- url     : https://prove2.me/theorems/c119d36f-30e2-4d74-b596-fa91adc93cdf
-- title:
--   Terminal residual expansion over a prescribed coefficient lattice
-- statement:
--   Given an integral subring of a rational algebra with reduction maps at every binary precision, canonical sections, the stated kernel control, and an interpolation grid, expand a lookup-separator contraction into residual networks over that same subring. The number of terms meets the global mode bound and the weights have a common denominator guard. The graph and precision bounds hold for the prescribed lattice, so its known reductions can be applied to the resulting congruence.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Section 5.3(i)–(ii), contraction with prescribed dyadic reductions.

import Definitions.Def_DetDLP_FactorBase
import Definitions.Def_DetDLP_TerminalBTN

set_option autoImplicit false
open Finset Polynomial

namespace DetDLP

theorem terminal_residual_expansion_over_a_prescribed_lattice (C : ℕ) :
    ∃ (L₀ : ℕ) (K₁ K₂ : ℝ),0 ≤ K₁ ∧ 0 ≤ K₂ ∧
    ∀ {G : BipartiteMultigraph} {b m k S p ell : ℕ}
      (spec : LookupSeparatorSpec G m k S (C*Nat.ceil ((b:ℝ)^((3:ℝ)/4)))),
    let L := Nat.clog 2 S
    let D := Nat.clog 32 (4*m)
    let κ := 4*L
    let g := 64*(S+1)*(L+1)*2^L*64^D
    let U := max (k+32*(L+2)) (2*(S/((L/32).sqrt+1)))
    L₀ ≤ L → 0 < m → b ≤ C*(4*m*k) → S ≤ C*m*b → m ≤ C*blockCount b → 0 < p → p ≤ S →
    ∀ (H : Type) [CommRing H] [Algebra ℚ H] (I : Subring H),
      (∀ q : ℚ,(q=0 ∨ 0 ≤ padicValRat 2 q)→algebraMap ℚ H q∈I) →
    ∀ (R : ℕ→Type) [∀ p,CommRing (R p)] [∀ p,Algebra (ZMod (2^p)) (R p)]
      (red : (p : ℕ)→I→+*R p) (lift : (p : ℕ)→R p→I)
      (grid : (p : ℕ)→Fin (2^κ)→R p),
      (∀ p,0 < p → ∀ x,red p (lift p x)=x) →
      (∀ p x,red p x=0→(2:I)^p∣x) →
      (∀ p i j,i≠j→IsUnit (grid p i-grid p j)) →
    ∀ T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→I,
      ∃ (N : ℕ) (w : Fin N→H) (R : Fin N→BipartiteMultigraph)
        (A : (l : Fin N)→(v : Fin (R l).nV)→(Fin ((R l).deg v)→Bool)→I),
        (N:ℝ) ≤ Real.exp (K₁*((b:ℝ)/(L:ℝ)^(7/40:ℝ))+K₂*(L:ℝ)^(13/10:ℝ)) ∧
        (∀ l,(R l).nE=4*m*k ∧ (R l).nV ≤ 4*m+64^D ∧ (R l).maxDeg ≤ U ∧ (2:H)^g*w l∈I) ∧
        ∃ err : I,(∑ l,w l*((BTNContract (R l) (A l):I):H))-((BTNContract G T:I):H)=(2:H)^p*(err:H) := by sorry

end DetDLP
