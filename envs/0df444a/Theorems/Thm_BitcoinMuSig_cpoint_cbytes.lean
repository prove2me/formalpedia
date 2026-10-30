-- Prove2me | Theorems.Thm_BitcoinMuSig_cpoint_cbytes
-- name    : BitcoinMuSig.cpoint_cbytes
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:35:54.122678+00:00
-- url     : https://prove2.me/theorems/f18f962b-981a-4cb9-ba0d-52b601801b95
-- title:
--   Compressed encoding round-trips
-- statement:
--   For reduced curve points: `cpoint (cbytes P) = some P`.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.cpoint_cbytes (P : ℕ × ℕ) (hP : onCurve P = true) (hx : P.1 < p) (hy : P.2 < p) :
    cpoint (cbytes P) = some P := by sorry
