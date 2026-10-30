-- Prove2me | Theorems.Thm_BitcoinMuSig_nsmul_Gpt_mem
-- name    : BitcoinMuSig.nsmul_Gpt_mem
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:33:50.727632+00:00
-- url     : https://prove2.me/theorems/e8a09743-2110-4532-afe4-beb9573a2056
-- title:
--   Multiples of the generator are killed by n
-- statement:
--   `n • (d • Gpt) = 0` for every $d$.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.nsmul_Gpt_mem (d : ℕ) : n • (d • Gpt) = 0 := by sorry
