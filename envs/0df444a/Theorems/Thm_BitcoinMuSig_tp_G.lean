-- Prove2me | Theorems.Thm_BitcoinMuSig_tp_G
-- name    : BitcoinMuSig.tp_G
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:32:58.498134+00:00
-- url     : https://prove2.me/theorems/6b20d8f7-8888-4722-9675-bf27e3fb92c5
-- title:
--   The executable generator is the Mathlib generator
-- statement:
--   `tp G = Gpt`.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.tp_G : tp G = Gpt := by sorry
