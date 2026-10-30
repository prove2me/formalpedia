-- Prove2me | Theorems.Thm_BitcoinMuSig_padd_comm
-- name    : BitcoinMuSig.padd_comm
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:30:26.066584+00:00
-- url     : https://prove2.me/theorems/5b17cabf-18f0-414c-ae82-59a8093370c4
-- title:
--   The executable addition is commutative
-- statement:
--   `padd P Q = padd Q P` for valid points.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.padd_comm (P Q : Point) (hP : Valid P) (hQ : Valid Q) :
    padd P Q = padd Q P := by sorry
