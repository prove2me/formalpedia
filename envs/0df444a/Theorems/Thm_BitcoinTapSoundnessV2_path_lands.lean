-- Prove2me | Theorems.Thm_BitcoinTapSoundnessV2_path_lands
-- name    : BitcoinTapSoundnessV2.path_lands
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T18:03:25.454276+00:00
-- url     : https://prove2.me/theorems/7edf8389-a2d8-4167-9a8e-70566839fbb2
-- title:
--   Walking a Merkle path lands on a subtree at the path's depth, or returns two colliding strings
-- statement:
--   For a tree $T$, a list of 32-byte path nodes and a 32-byte starting hash $h$ with `nodes.foldl tapbranchHash h = T.hash`: either `walk T nodes h = .inl U` for a subtree $U$ of $T$ at depth equal to the number of nodes with `U.hash = h`, or `walk T nodes h = .inr (x, y)` with `Collides x y`. The collision, when there is one, is the pair `walk` computes from the inputs.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyTaprootCommitment, ComputeTaprootMerkleRoot, ComputeTapleafHash, ComputeTapbranchHash (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash (src/pubkey.cpp); secp256k1_xonly_pubkey_tweak_add_check; BIP341

import Definitions.Def_BitcoinTapSoundnessV2
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinTaproot
open BitcoinTapSoundnessV2 BitcoinSer BitcoinTaproot

theorem BitcoinTapSoundnessV2.path_lands (T : BitcoinTapSoundnessV2.TapTree) (nodes : List BitcoinSer.Bytes) (h : BitcoinSer.Bytes)
    (hn : ∀ n ∈ nodes, n.length = 32) (hh : h.length = 32) (heq : nodes.foldl BitcoinTaproot.tapbranchHash h = T.hash) :
    (∃ U, BitcoinTapSoundnessV2.walk T nodes h = .inl U ∧ U ∈ T.subtreesAt nodes.length ∧ U.hash = h) ∨
      (∃ x y, BitcoinTapSoundnessV2.walk T nodes h = .inr (x, y) ∧ BitcoinTapSoundnessV2.Collides x y) := by sorry
