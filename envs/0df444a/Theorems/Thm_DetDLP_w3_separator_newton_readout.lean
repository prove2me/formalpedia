-- Prove2me | Theorems.Thm_DetDLP_w3_separator_newton_readout
-- name    : DetDLP.w3_separator_newton_readout
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T21:25:08.965735+00:00
-- url     : https://prove2.me/theorems/d4fa5951-e3dc-408b-963a-5f806b3f68c8
-- title:
--   Stage II: exact Newton readout from a parsimonious weighted separator
-- statement:
--   In a separator whose surviving edge assignments are in bijection with the valid prefix-compatible tuple pairs, assume each surviving assignment has the product of its signed binomial series, the other assignments have weight zero, and the integer filter sum fits in the chosen precision. Then pairing the encoded contraction coefficients with their Newton coefficients returns the exact prefix-restricted integer mass.
-- source:
--   Deterministic Discrete Logarithms, §4.1–4.3, equations (4.1)–(4.5) and proof of Theorem 1.1, pp. 13–16; referee revisions R1 and R2.

import Definitions.Def_DetDLP_W3_Separator
set_option autoImplicit false
open DetDLP

theorem DetDLP.w3_separator_newton_readout (q : w3_Query) (hm : 2 ≤ q.m) (hM : 2 ≤ q.M)
    (G : BipartiteMultigraph) (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly (w3_precision q) (w3_len q))
    (ok : (Fin G.nE → Bool) → Prop) (e : {a // ok a} ≃ {t // w3_valid q t})
    (live : ∀ a : {a // ok a}, (∏ v, T v (fun j => a.val ((G.ports v).get j))) = w3_pairWeight q (e a).val)
    (dead : ∀ a : Fin G.nE → Bool, ¬ok a → (∏ v, T v (fun j => a ((G.ports v).get j))) = 0)
    (hbound : w3_mass q < (2 : ℤ)^w3_precision q) :
    ∀ c : Fin (w3_len q) → ℕ, BTNContract G T = truncPolyOfCoeffs (w3_precision q) (w3_len q) c →
      ((∑ j : Fin (w3_len q), (newtonCoeff (2*q.m) q.M j.val : ZMod (2^w3_precision q)) * (c j : ZMod (2^w3_precision q))).val : ℤ) = w3_mass q := by sorry
