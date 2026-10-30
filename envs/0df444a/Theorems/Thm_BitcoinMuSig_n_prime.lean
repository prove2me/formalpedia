-- Prove2me | Theorems.Thm_BitcoinMuSig_n_prime
-- name    : BitcoinMuSig.n_prime
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:34:16.967349+00:00
-- url     : https://prove2.me/theorems/6d72948c-3721-4ae7-ba09-4244e9a5b2b7
-- title:
--   The group order n of secp256k1 is prime
-- statement:
--   `Nat.Prime n`, by a recursive Lucas–Pratt certificate.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.n_prime : Nat.Prime n := by sorry
