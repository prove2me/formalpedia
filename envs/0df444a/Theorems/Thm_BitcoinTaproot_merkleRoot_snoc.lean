-- Prove2me | Theorems.Thm_BitcoinTaproot_merkleRoot_snoc
-- name    : BitcoinTaproot.merkleRoot_snoc
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T16:34:50.666867+00:00
-- url     : https://prove2.me/theorems/9924e684-e4c6-4dc3-bf64-7debb9effa76
-- title:
--   Appending a path node hashes the root with it
-- statement:
--   For a well-formed control block (length $33 + 32k$) and a 32-byte node: `taprootMerkleRoot (control ++ node) leaf = tapbranchHash (taprootMerkleRoot control leaf) node`. The merkle root is a left fold of the branch hash along the path.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyWitnessProgram (version 1), ExecuteWitnessScript, EvalScript under SigVersion::TAPSCRIPT, EvalChecksigTapscript, CheckSchnorrSignature, SignatureHashSchnorr, ComputeTapleafHash, ComputeTapbranchHash, ComputeTaprootMerkleRoot, VerifyTaprootCommitment, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash, src/pubkey.cpp; secp256k1_xonly_pubkey_tweak_add_check, src/secp256k1/src/modules/extrakeys/main_impl.h; IsOpSuccess, src/script/script.cpp; BIP340, BIP341, BIP342 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinTaproot
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.merkleRoot_snoc (control node leaf : Bytes)
    (hc : BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE ≤ control.length)
    (hm : (control.length - BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE) % BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE = 0)
    (hn : node.length = BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE) :
    BitcoinTaproot.taprootMerkleRoot (control ++ node) leaf =
      BitcoinTaproot.tapbranchHash (BitcoinTaproot.taprootMerkleRoot control leaf) node := by sorry
