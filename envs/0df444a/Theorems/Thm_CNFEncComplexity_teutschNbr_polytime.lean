-- Prove2me | Theorems.Thm_CNFEncComplexity_teutschNbr_polytime
-- name    : CNFEncComplexity.teutschNbr_polytime
-- status  : Proved
-- author  : @bersubs
-- created : 2026-11-14T18:19:07.539202+00:00
-- url     : https://prove2.me/theorems/e800c275-b22c-4d5f-8a81-9282f7a53524
-- title:
--   Binary TM simulation of Teutsch’s folded disperser neighbor queries
-- statement:
--   Let $P$ be a fixed, coin-free log-cost RAM program and let $e,C,a$ be fixed natural numbers. On a binary query $(N,k,\ell,i)$, set $n=\lfloor\log_2 N\rfloor+1$ and use the degree budget $a n^a$ to decode $i$ into a layer and a local slot. Reject layers outside the range of $k$ or above $\lfloor\log_2 N\rfloor$, and reject $\ell\ge N$.
--
--   For a valid layer $j$, simulate $P$ on $(n,j,\ell)$ for $n^e+e$ steps starting with zero-filled memory elsewhere. Treat a halted state’s cell zero as the list length and cells $1,2,\ldots$ as the entries. An existing entry at the decoded slot is folded by a power-of-two residue and copy index and translated into its disjoint layer interval. The query returns no label when the program has not halted or the slot is out of range.
--
--   The resulting optional label function has a deterministic multitape Turing machine running in time polynomial in the binary query length. The machine may depend on $P,e,C,a$. The result supplies the bit-model implementation of the explicit neighbor algorithm independently of the disperser coverage theorem.
--
--   **Formalization Note** The query and result are encoded by `encNbrIn` and `encOptNat`. The functions `mergeNbr` and `ramFoldedLayer` specify the slot decoding, folding and treatment of invalid inputs.
-- source:
--   Jason Teutsch, Short lists for shortest descriptions in short time, https://arxiv.org/pdf/1212.6104, §4, pp. 6–8, Theorem 4 and Expander Lemma (binary machine implementation of the neighbor algorithm).

import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_CNFEncComplexity_encNbrIn
import Definitions.Def_CNFEncComplexity_teutschNbr

namespace CNFEncComplexity

/-- The binary evaluator for the disjoint union of folded log-cost RAM neighbor lists
has a polynomial-time multitape implementation. -/
theorem teutschNbr_polytime (P : TimeSpaceMA.Program) (e C a : ℕ)
    (hP : P.CoinFree) :
    Nonempty (Turing.TM2ComputableInPolyTime encNbrIn encOptNat
      (mergeNbr (fun N => a * (Nat.log 2 N + 1)^a) (ramFoldedLayer P e C))) := by sorry

end CNFEncComplexity
