-- Prove2me | Theorems.Thm_BitcoinTapSoundnessV2_tagged_pre
-- name    : BitcoinTapSoundnessV2.tagged_pre
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T18:02:28.56727+00:00
-- url     : https://prove2.me/theorems/b47de5e9-eab7-43b8-8dc9-03afff6cfd32
-- title:
--   A tagged hash is the SHA-256 of its preimage
-- statement:
--   `tagged t m = sha256 (taggedPre t m)`, by definition of `taggedHash`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyTaprootCommitment, ComputeTaprootMerkleRoot, ComputeTapleafHash, ComputeTapbranchHash (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash (src/pubkey.cpp); secp256k1_xonly_pubkey_tweak_add_check; BIP341

import Definitions.Def_BitcoinTapSoundnessV2
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinTaproot
open BitcoinTapSoundnessV2 BitcoinSer BitcoinTaproot

theorem BitcoinTapSoundnessV2.tagged_pre (t : String) (m : BitcoinSer.Bytes) :
    BitcoinTaproot.tagged t m = BitcoinSer.sha256 (BitcoinTapSoundnessV2.taggedPre t m) := by sorry
