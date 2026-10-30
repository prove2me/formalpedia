-- Prove2me | Theorems.Thm_BitcoinTapSoundnessV2_leaf_ne_branch
-- name    : BitcoinTapSoundnessV2.leaf_ne_branch
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T18:03:02.40032+00:00
-- url     : https://prove2.me/theorems/5bb52627-3589-44ab-a746-083bdfbd674c
-- title:
--   A leaf hash equal to a branch hash: the TapLeaf and TapBranch preimages collide
-- statement:
--   For any leaf version $v$, script $s$ and byte strings $a, b$: `tapleafHash v s = tapbranchHash a b` implies `Collides (taggedPre "TapLeaf" (leafMsg v s)) (taggedPre "TapBranch" (branchMsg a b))`. The two strings differ in their first 32 bytes (`tapleaf_ne_tapbranch`).
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyTaprootCommitment, ComputeTaprootMerkleRoot, ComputeTapleafHash, ComputeTapbranchHash (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash (src/pubkey.cpp); secp256k1_xonly_pubkey_tweak_add_check; BIP341

import Definitions.Def_BitcoinTapSoundnessV2
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinTaproot
open BitcoinTapSoundnessV2 BitcoinSer BitcoinTaproot

theorem BitcoinTapSoundnessV2.leaf_ne_branch (v : BitcoinSer.Byte) (s a b : BitcoinSer.Bytes)
    (h : BitcoinTaproot.tapleafHash v s = BitcoinTaproot.tapbranchHash a b) :
    BitcoinTapSoundnessV2.Collides (BitcoinTapSoundnessV2.taggedPre "TapLeaf" (BitcoinTapSoundnessV2.leafMsg v s))
      (BitcoinTapSoundnessV2.taggedPre "TapBranch" (BitcoinTapSoundnessV2.branchMsg a b)) := by sorry
