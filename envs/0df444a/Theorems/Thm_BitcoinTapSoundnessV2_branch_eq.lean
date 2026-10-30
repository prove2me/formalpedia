-- Prove2me | Theorems.Thm_BitcoinTapSoundnessV2_branch_eq
-- name    : BitcoinTapSoundnessV2.branch_eq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T18:03:15.365543+00:00
-- url     : https://prove2.me/theorems/085cda03-d2e1-46d0-bf18-9ed5bea415f6
-- title:
--   Equal branch hashes of 32-byte children have the same children up to order, or the two TapBranch preimages collide
-- statement:
--   For 32-byte strings $a, b, c, d$: `tapbranchHash a b = tapbranchHash c d` implies $(a = c \land b = d) \lor (a = d \land b = c)$, or `Collides (taggedPre "TapBranch" (branchMsg a b)) (taggedPre "TapBranch" (branchMsg c d))`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyTaprootCommitment, ComputeTaprootMerkleRoot, ComputeTapleafHash, ComputeTapbranchHash (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash (src/pubkey.cpp); secp256k1_xonly_pubkey_tweak_add_check; BIP341

import Definitions.Def_BitcoinTapSoundnessV2
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinTaproot
open BitcoinTapSoundnessV2 BitcoinSer BitcoinTaproot

theorem BitcoinTapSoundnessV2.branch_eq (a b c d : BitcoinSer.Bytes) (ha : a.length = 32) (hb : b.length = 32)
    (hc : c.length = 32) (hd : d.length = 32) (h : BitcoinTaproot.tapbranchHash a b = BitcoinTaproot.tapbranchHash c d) :
    ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∨
      BitcoinTapSoundnessV2.Collides (BitcoinTapSoundnessV2.taggedPre "TapBranch" (BitcoinTapSoundnessV2.branchMsg a b))
        (BitcoinTapSoundnessV2.taggedPre "TapBranch" (BitcoinTapSoundnessV2.branchMsg c d)) := by sorry
