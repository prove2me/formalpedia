-- Prove2me | Theorems.Thm_BitcoinTapSoundnessV2_tagged_collision
-- name    : BitcoinTapSoundnessV2.tagged_collision
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T18:02:40.918707+00:00
-- url     : https://prove2.me/theorems/7c605365-a06c-4d48-a566-8772c8762be6
-- title:
--   Equal tagged hashes have equal tag hashes and messages, or their two preimages collide
-- statement:
--   For tags $t, t'$ and messages $m, m'$: if `tagged t m = tagged t' m'` then either `sha256 (ascii t) = sha256 (ascii t')` and $m = m'$, or `Collides (taggedPre t m) (taggedPre t' m')`: the two explicit 64-byte-prefixed preimages differ and hash alike.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyTaprootCommitment, ComputeTaprootMerkleRoot, ComputeTapleafHash, ComputeTapbranchHash (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash (src/pubkey.cpp); secp256k1_xonly_pubkey_tweak_add_check; BIP341

import Definitions.Def_BitcoinTapSoundnessV2
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinSig
open BitcoinTapSoundnessV2 BitcoinSer BitcoinTaproot

theorem BitcoinTapSoundnessV2.tagged_collision (t t' : String) (m m' : BitcoinSer.Bytes)
    (h : BitcoinTaproot.tagged t m = BitcoinTaproot.tagged t' m') :
    (BitcoinSer.sha256 (BitcoinSig.ascii t) = BitcoinSer.sha256 (BitcoinSig.ascii t') ∧ m = m') ∨
      BitcoinTapSoundnessV2.Collides (BitcoinTapSoundnessV2.taggedPre t m) (BitcoinTapSoundnessV2.taggedPre t' m') := by sorry
