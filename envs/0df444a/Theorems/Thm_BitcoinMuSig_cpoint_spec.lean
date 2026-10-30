-- Prove2me | Theorems.Thm_BitcoinMuSig_cpoint_spec
-- name    : BitcoinMuSig.cpoint_spec
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:35:26.714665+00:00
-- url     : https://prove2.me/theorems/69e5b183-637b-4d33-a59b-1dc8b88d8e01
-- title:
--   Parsed compressed points are reduced curve points
-- statement:
--   `cpoint b = some P → onCurve P ∧ P.1 < p ∧ P.2 < p`.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
import Definitions.Def_BitcoinSer
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.cpoint_spec (b : BitcoinSer.Bytes) (P : ℕ × ℕ) (h : cpoint b = some P) :
    onCurve P = true ∧ P.1 < p ∧ P.2 < p := by sorry
