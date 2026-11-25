-- Prove2me | Theorems.Thm_DetDLP_guard_cleared_finite_residual_contraction
-- name    : DetDLP.guard_cleared_finite_residual_contraction
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T19:04:24.317709+00:00
-- url     : https://prove2.me/theorems/d529d631-acd0-4eb0-9e17-a802f00d29ce
-- title:
--   Guard-cleared contraction identity over finite coefficient rings and the residual logarithmic degree scale
-- statement:
--   For lookup-separator networks in the scaling regime of Theorem 4.3, take the explicitly guarded precision and a binary irreducible modulus. Over the truncated polynomial ring of the resulting finite extension, the original contraction multiplied by the common power of two is exactly a weighted sum of residual contractions. The networks have the stated edge and vertex counts. For each residual graph both its maximum degree and its rounded scalar degree cutoff, multiplied by the block count, are bounded by a constant times the original bit parameter. Its scalar logarithmic degree parameter therefore controls the logarithm of the block count. The number of residual terms obeys the global expansion bound.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Section 5.3, guarded contraction in the finite extension and application of the scalar degree bound.

import Definitions.Def_DetDLP_FactorBase
import Definitions.Def_DetDLP_TerminalBTN

set_option autoImplicit false
open Finset Polynomial

namespace DetDLP

theorem guard_cleared_finite_residual_contraction (C : ℕ) :
    ∃ (L₀ : ℕ) (K₁ K₂ : ℝ),0 ≤ K₁ ∧ 0 ≤ K₂ ∧
    ∀ {G : BipartiteMultigraph} {b m k S p ell : ℕ}
      (spec : LookupSeparatorSpec G m k S (C*Nat.ceil ((b:ℝ)^((3:ℝ)/4)))),
    let L := Nat.clog 2 S
    let D := Nat.clog 32 (4*m)
    let κ := 4*L
    let g := 64*(S+1)*(L+1)*2^L*64^D
    let J := 1217*(C+1)^3
    L₀ ≤ L → 0 < b → 0 < m → b ≤ C*(4*m*k) → 4*m*k ≤ C*b → S ≤ C*m*b → m ≤ C*blockCount b → 0 < p → p ≤ S →
    ∃ c : Fin κ→ZMod 2,let f := (X:ℤ[X])^κ+∑ j,monomial j.val ((c j).val:ℤ)
    f.Monic ∧ f.natDegree=κ ∧ Irreducible (f.map (Int.castRingHom (ZMod 2))) ∧
    let B₀ := AdjoinRoot (f.map (Int.castRingHom (ZMod (2^(p+g)))))
    let B := AdjoinRoot ((X:B₀[X])^ell)
    ∀ T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→B,
      ∃ (N : ℕ) (w : Fin N→B) (R : Fin N→BipartiteMultigraph)
        (A : (j : Fin N)→(v : Fin (R j).nV)→(Fin ((R j).deg v)→Bool)→B),
        (N:ℝ) ≤ Real.exp (K₁*((b:ℝ)/(L:ℝ)^(7/40:ℝ))+K₂*(L:ℝ)^(13/10:ℝ)) ∧
        (∀ j,(R j).nE=4*m*k ∧ (R j).nV ≤ 4*m+64^D ∧
          let Δ := max (R j).maxDeg (Nat.ceil ((b:ℝ)^((9:ℝ)/10)))
          let ρ := max 1 (Nat.floor (Real.logb 2 ((b:ℝ)/(Δ:ℝ))))
          Δ*m ≤ J*b ∧ logSafe m ≤ ((J:ℝ)+2)*ρ) ∧
        (∑ j,w j*BTNContract (R j) (A j))=(2:B)^g*BTNContract G T := by sorry

end DetDLP
