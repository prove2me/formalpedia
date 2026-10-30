-- Prove2me | Theorems.Thm_BitcoinTapSoundnessV2_commitment_soundness
-- name    : BitcoinTapSoundnessV2.commitment_soundness
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T18:03:50.531612+00:00
-- url     : https://prove2.me/theorems/f8b0ce84-8ed5-4e45-ac3c-a4c74b08c074
-- title:
--   Script-path soundness at the commitment level: VerifyTaprootCommitment opens only committed leaves, or names an explicit SHA-256 or tweak collision
-- statement:
--   For an output key $q$, internal key `internal32`, parity bit and tree $T$ with `HonestOutput q internal32 parity T`, and any control block of length $33 + 32k$ whose internal-key bytes are `internal32` and parity bit is `parity`, and any leaf $(v, s)$ with `verifyTaprootCommitment control q (tapleafHash v s) = true`, writing `root` for `taprootMerkleRoot control (tapleafHash v s)`, one of:
--
--   1. `root = T.hash`, and either `scriptPathWitness T control v s = none` with `tapleafHash v s ∈ T.leaves`, or it is `some (x, y)` with `Collides x y`;
--   2. `root ≠ T.hash` and `Collides (taggedPre "TapTweak" (internal32 ++ root)) (taggedPre "TapTweak" (internal32 ++ T.hash))`;
--   3. `root ≠ T.hash` and, for the point $P$ with `liftX (beVal internal32) = some P`, `TweakCollision q parity P (tapTweakHash internal32 root) (tapTweakHash internal32 T.hash)`: the two 32-byte tweak hashes differ and both carry $P$ to $q$.
--
--   Every collision is an explicit pair of strings computed from the inputs. This is the BIP341 claim that a spender cannot open a leaf the output's creator did not commit to, stated as a reduction to SHA-256 collision resistance and to the hardness of finding two tweaks for one output key.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyTaprootCommitment, ComputeTaprootMerkleRoot, ComputeTapleafHash, ComputeTapbranchHash (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash (src/pubkey.cpp); secp256k1_xonly_pubkey_tweak_add_check; BIP341

import Definitions.Def_BitcoinTapSoundnessV2
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinSig
open BitcoinTapSoundnessV2 BitcoinSer BitcoinTaproot

theorem BitcoinTapSoundnessV2.commitment_soundness (q internal32 : BitcoinSer.Bytes) (parity : Bool)
    (T : BitcoinTapSoundnessV2.TapTree) (hT : BitcoinTapSoundnessV2.HonestOutput q internal32 parity T)
    (control : BitcoinSer.Bytes) (k : Nat)
    (hc : control.length = BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE + BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE * k)
    (hkey : BitcoinTapSoundnessV2.controlInternalKey control = internal32) (hpar : BitcoinTapSoundnessV2.controlParity control = parity)
    (v : BitcoinSer.Byte) (s : BitcoinSer.Bytes)
    (h : BitcoinTaproot.verifyTaprootCommitment control q (BitcoinTaproot.tapleafHash v s) = true) :
    (BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s) = T.hash ∧
      ((BitcoinTapSoundnessV2.scriptPathWitness T control v s = none ∧ BitcoinTaproot.tapleafHash v s ∈ T.leaves) ∨
        (∃ x y, BitcoinTapSoundnessV2.scriptPathWitness T control v s = some (x, y) ∧ BitcoinTapSoundnessV2.Collides x y))) ∨
    (BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s) ≠ T.hash ∧
      BitcoinTapSoundnessV2.Collides
        (BitcoinTapSoundnessV2.taggedPre "TapTweak" (internal32 ++ BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s)))
        (BitcoinTapSoundnessV2.taggedPre "TapTweak" (internal32 ++ T.hash))) ∨
    (BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s) ≠ T.hash ∧
      ∃ P, BitcoinSig.liftX (BitcoinSig.beVal internal32) = some P ∧
        BitcoinTapSoundnessV2.TweakCollision q parity P
          (BitcoinTaproot.tapTweakHash internal32 (BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s)))
          (BitcoinTaproot.tapTweakHash internal32 T.hash)) := by sorry
