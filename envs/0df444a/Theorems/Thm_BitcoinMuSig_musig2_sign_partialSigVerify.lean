-- Prove2me | Theorems.Thm_BitcoinMuSig_musig2_sign_partialSigVerify
-- name    : BitcoinMuSig.musig2_sign_partialSigVerify
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T00:37:08.26882+00:00
-- url     : https://prove2.me/theorems/ecfc58f9-2b35-48c5-a4a1-780cccd5e117
-- title:
--   An honest BIP327 Sign output passes the partial check
-- statement:
--   With $s = \varepsilon k_1 + b\varepsilon k_2 + e\,a\,g\,g_{acc}\,d$: $sG = \varepsilon(k_1G + b\,k_2G) + (e\,a\,g\,g_{acc})(dG)$.
-- source:
--   BIP327 MuSig2 for BIP340-compatible multi-signatures (KeyAgg, ApplyTweak, NonceAgg, GetSessionValues, PartialSigVerifyInternal, PartialSigAgg): https://github.com/bitcoin/bips/blob/master/bip-0327.mediawiki; BIP340 Schnorr signatures; RFC 9591 FROST (Lagrange-coefficient aggregation); secp256k1 (SEC 2); Mathlib's WeierstrassCurve.Affine group law; the signature mission's executable curve (BitcoinSig.padd, pmul, schnorrVerify)

import Definitions.Def_BitcoinMuSig
open BitcoinMuSig BitcoinSig BitcoinTaproot

theorem BitcoinMuSig.musig2_sign_partialSigVerify {K M : Type*} [CommRing K] [AddCommGroup M]
    [Module K M] (G : M) (d k₁ k₂ a b e g gacc ε : K) :
    (ε * k₁ + b * (ε * k₂) + e * a * (g * gacc * d)) • G =
      ε • (k₁ • G + b • (k₂ • G)) + (e * a * (g * gacc)) • (d • G) := by sorry
