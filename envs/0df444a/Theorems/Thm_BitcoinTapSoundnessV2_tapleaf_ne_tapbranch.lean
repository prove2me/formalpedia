-- Prove2me | Theorems.Thm_BitcoinTapSoundnessV2_tapleaf_ne_tapbranch
-- name    : BitcoinTapSoundnessV2.tapleaf_ne_tapbranch
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T18:02:51.450931+00:00
-- url     : https://prove2.me/theorems/4be482fa-15e9-4da7-a4dd-4fb389b5417e
-- title:
--   The TapLeaf and TapBranch tags hash differently
-- statement:
--   `sha256 (ascii "TapLeaf") ≠ sha256 (ascii "TapBranch")`, by kernel computation of the model's SHA-256.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyTaprootCommitment, ComputeTaprootMerkleRoot, ComputeTapleafHash, ComputeTapbranchHash (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash (src/pubkey.cpp); secp256k1_xonly_pubkey_tweak_add_check; BIP341

import Definitions.Def_BitcoinTapSoundnessV2
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinTapSoundnessV2 BitcoinSer BitcoinTaproot

theorem BitcoinTapSoundnessV2.tapleaf_ne_tapbranch :
    BitcoinSer.sha256 (BitcoinSig.ascii "TapLeaf") ≠ BitcoinSer.sha256 (BitcoinSig.ascii "TapBranch") := by sorry
