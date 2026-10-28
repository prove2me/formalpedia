-- Prove2me | Theorems.Thm_BitcoinBIP68_decode_sequence
-- name    : BitcoinBIP68.decode_sequence
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T01:35:18.659633+00:00
-- url     : https://prove2.me/theorems/90cbf79f-312f-416c-8083-2f0c7b9f3ccd
-- title:
--   BIP68 sequence masks agree with arithmetic decoding
-- statement:
--   Let $s$ be any unsigned 32-bit word and $n$ its value. Put $d=n\bmod65536$. The implementation's disable-bit and time-type tests agree with the corresponding quotient-and-remainder tests, its masked delay is $d$, and its masked left-shifted seconds value is $512d$:
--
--   $$\begin{aligned}
--   \mathrm{disabled}_{\mathrm{core}}(s)&\iff\lfloor n/2^{31}\rfloor=1,\\
--   \mathrm{time}_{\mathrm{core}}(s)&\iff\lfloor n/2^{22}\rfloor\bmod2=1,\\
--   \mathrm{delay}_{\mathrm{core}}(s)&=d,\\
--   \mathrm{seconds}_{\mathrm{core}}(s)&=512d.
--   \end{aligned}$$
--
--   The statement includes every bit pattern and makes no hypothesis on the unused bits. It connects the bit-vector implementation to the arithmetic specification, including the fact that the masked nine-bit shift loses no significant bits.
-- source:
--   BIP68, Specification and Implementation: https://github.com/bitcoin/bips/blob/100ba872c808946155b1eeb8c4568058f2eea0a7/bip-0068.mediawiki; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, CalculateSequenceLocks (lines 45–101), EvaluateSequenceLocks (103–111), SequenceLocks (113–116): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/tx_verify.cpp#L45-L116. Functional contract extracted from these routines; the BIP does not number these claims as mathematical theorems.

import Definitions.Def_BIP68_Model
import Definitions.Def_BIP68_Core

theorem BitcoinBIP68.decode_sequence (sequence : BitVec 32) :
    (BitcoinBIP68.coreDisabled sequence = true ↔ BitcoinBIP68.specDisabled sequence) ∧
    (BitcoinBIP68.coreTimeBased sequence = true ↔ BitcoinBIP68.specTimeBased sequence) ∧
    BitcoinBIP68.coreDelay sequence = BitcoinBIP68.specDelay sequence ∧
    BitcoinBIP68.coreSeconds sequence = 512 * BitcoinBIP68.specDelay sequence := by sorry
