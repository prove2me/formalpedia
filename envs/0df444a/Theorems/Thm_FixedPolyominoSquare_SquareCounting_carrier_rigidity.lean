-- Prove2me | Theorems.Thm_FixedPolyominoSquare_SquareCounting_carrier_rigidity
-- name    : FixedPolyominoSquare.SquareCounting.carrier_rigidity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:48.761482+00:00
-- url     : https://prove2.me/theorems/b4984a47-9e5b-474e-82fb-c145288ff211
-- title:
--   Lemma 7.1 — local geometric rigidity
-- statement:
--   Use the exact cavity, body-square, address, dent and bump coordinates of Section 7. For each allowed opening vector, tile type and normalized label datum, both local rigidity conclusions hold:
--
--   $$\text{no three consecutive body cells of any row or column are all absent},$$
--
--   and body rows and columns 1 and 2, together with every three-by-three body corner, are intact. The statement applies to any finite Wang inventory and any integer rectangle constant $R\geq2$, with $s_{\rm amp}=1024R^3$, $K_s=4s_{\rm amp}\max(H_{\rm col},V_{\rm col})$ and $P_s=K_s+4M_W+64$.
--
--   These are geometric assertions about unlabelled supports, rather than conditions stored in the carrier datum. Specializing to the source's $W_{\rm prod}$ and $R_{\rm rect}$ recovers its two assertions.
--
--   Differences from the source:
--   - generalization: the Section 7 carriers for Wprod and its integer rectangle bound Rrect≥2 → the identical carrier formula for every finite Wang system W and every integer R≥2; reason: the local rigidity assertion depends only on the stated coordinates and separations; Wprod and Rrect are an included specialization
--   - encoding: fixed colour and tile bijections j,iotaH,iotaV → tile types and colours already numbered by their Fin indices; reason: these indices are the allowed fixed bijections and change no geometric support after choosing those bijections
-- source:
--   Qiuyu Chen, Ba'ao Xie, STOC 2027 submission #219 (October 2026), p. 17, Lemma 7.1; pp. 16–17, carrier construction

import Definitions.Def_FixedPolyominoSquare_SquareCounting_Carriers

namespace FixedPolyominoSquare.SquareCounting

/-- Chen--Xie, Lemma 7.1, p. 17, for the same coordinates and any finite
Wang inventory; specialize to Wprod and its stated rectangle constant. -/
theorem carrier_rigidity (W : WangSystem) (R : ℕ) (hR : 2 ≤ R) (d : CarrierData W R) :
    ((∀ p : Cell, p ∈ square (Ps W R) → p + (1, 0) ∈ square (Ps W R) →
        p + (2, 0) ∈ square (Ps W R) →
        p ∈ carrier W R d ∨ p + (1, 0) ∈ carrier W R d ∨ p + (2, 0) ∈ carrier W R d) ∧
      (∀ p : Cell, p ∈ square (Ps W R) → p + (0, 1) ∈ square (Ps W R) →
        p + (0, 2) ∈ square (Ps W R) →
        p ∈ carrier W R d ∨ p + (0, 1) ∈ carrier W R d ∨ p + (0, 2) ∈ carrier W R d)) ∧
    (∀ p ∈ square (Ps W R),
      (p.1 = 1 ∨ p.1 = 2 ∨ p.2 = 1 ∨ p.2 = 2 ∨
        ((p.1 < 3 ∨ (Ps W R : ℤ) - 3 ≤ p.1) ∧
          (p.2 < 3 ∨ (Ps W R : ℤ) - 3 ≤ p.2))) → p ∈ carrier W R d) := by sorry

end FixedPolyominoSquare.SquareCounting
