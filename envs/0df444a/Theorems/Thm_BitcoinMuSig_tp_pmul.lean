-- Prove2me | Theorems.Thm_BitcoinMuSig_tp_pmul
-- name    : BitcoinMuSig.tp_pmul
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:28:43.23926+00:00
-- url     : https://prove2.me/theorems/38fb9c33-f1c9-44b3-a73d-7f85af82e804
-- title:
--   The executable scalar multiplication is Mathlib's scalar action
-- statement:
--   For valid $P$ and $k < 2^{257}$: `tp (pmul k P) = k • tp P`.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.tp_pmul (k : ℕ) (P : Point) (hP : Valid P) (hk : k < 2 ^ 257) :
    tp (pmul k P) = k • tp P := by sorry
