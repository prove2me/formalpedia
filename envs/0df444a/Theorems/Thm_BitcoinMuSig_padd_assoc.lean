-- Prove2me | Theorems.Thm_BitcoinMuSig_padd_assoc
-- name    : BitcoinMuSig.padd_assoc
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:30:55.522788+00:00
-- url     : https://prove2.me/theorems/f1fd24f7-ba98-488d-977c-f402cbcd2367
-- title:
--   The executable addition is associative
-- statement:
--   For valid, reduced points: `padd (padd P Q) R = padd P (padd Q R)`. This is the group law the signature mission's executable curve lacked a proof of.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.padd_assoc (P Q R : Point) (hP : Valid P) (hQ : Valid Q) (hR : Valid R)
    (hPr : Reduced P) (hQr : Reduced Q) (hRr : Reduced R) :
    padd (padd P Q) R = padd P (padd Q R) := by sorry
