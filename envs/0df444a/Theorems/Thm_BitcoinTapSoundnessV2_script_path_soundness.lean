-- Prove2me | Theorems.Thm_BitcoinTapSoundnessV2_script_path_soundness
-- name    : BitcoinTapSoundnessV2.script_path_soundness
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T18:03:35.676298+00:00
-- url     : https://prove2.me/theorems/baa0266b-8c5c-46de-8eac-899ecb61a3b6
-- title:
--   Script-path soundness at the Merkle level: a verified path opens a committed leaf, or scriptPathWitness names a collision
-- statement:
--   For a tree $T$, a control block of length $33 + 32k$, a leaf version $v$ and a script $s$ with `taprootMerkleRoot control (tapleafHash v s) = T.hash`: either `scriptPathWitness T control v s = none` and `tapleafHash v s ∈ T.leaves`, or `scriptPathWitness T control v s = some (x, y)` with `Collides x y`.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyTaprootCommitment, ComputeTaprootMerkleRoot, ComputeTapleafHash, ComputeTapbranchHash (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash (src/pubkey.cpp); secp256k1_xonly_pubkey_tweak_add_check; BIP341

import Definitions.Def_BitcoinTapSoundnessV2
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinTaproot
open BitcoinTapSoundnessV2 BitcoinSer BitcoinTaproot

theorem BitcoinTapSoundnessV2.script_path_soundness (T : BitcoinTapSoundnessV2.TapTree) (control : BitcoinSer.Bytes) (k : Nat)
    (hc : control.length = BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE + BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE * k)
    (v : BitcoinSer.Byte) (s : BitcoinSer.Bytes)
    (h : BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s) = T.hash) :
    (BitcoinTapSoundnessV2.scriptPathWitness T control v s = none ∧ BitcoinTaproot.tapleafHash v s ∈ T.leaves) ∨
      (∃ x y, BitcoinTapSoundnessV2.scriptPathWitness T control v s = some (x, y) ∧ BitcoinTapSoundnessV2.Collides x y) := by sorry
