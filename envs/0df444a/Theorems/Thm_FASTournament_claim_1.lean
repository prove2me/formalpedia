-- Prove2me | Theorems.Thm_FASTournament_claim_1
-- name    : FASTournament.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:34:35.90216+00:00
-- url     : https://prove2.me/theorems/36182b3c-80b4-4aee-af7a-5a20f1e7ded3
-- title:
--   Claim 1 — $G_1$ has exactly the 41 listed minimal feedback arc sets
-- statement:
--   Let $\mathcal F$ be the family of all minimal feedback arc sets of $G_1$. Then $|\mathcal F|=41$ and
--   $$
--   \begin{aligned}
--   \mathcal F=\{&ehj, afhk, dgjo, acehk, acehn, acghk, bdejl, beijl, bfikl, cehin, cgikl, cgino, degjl, dgjkl,\\
--   &abdfkl, acdgkl, acdgko, acdgno, acghno, adfgkl, adfgko, adghjk, aefhmn, afhmno, bceikl, bceiln,\\
--   &bdejmo, bdfjkl, bdfjmo, bfimno, cegijl, cegiln, cehikl, abdfkmo, abdfmno, adfgmno, adfhjmo,\\
--   &bceimno, befhimn, befilmn, beijmno\},
--   \end{aligned}
--   $$
--   where the letters $a,b,\dots,o$ denote the arcs $12,23,34,45,51,13,35,52,24,41,16,26,63,64,65$ of $G_1$ in this order; for instance $ehj$ is the minimal FAS consisting of the arcs $51$, $52$ and $41$.
--
--   The incidence vectors of these sets are the rows of the $41\times 15$ matrix to which Lemma 4.3 is applied in the proof of Lemma 4.1.
--
--   **Formalization Note** An arc of $G_1$ (vertices `Fin 6`) is written as the pair of its 1-based endpoints; each letter is decoded through the list $E_1$.
--
--   Differences from the source:
--   - encoding: cycle (directed) → IsDirCycle: the arc set of a closed walk through k ≥ 2 distinct vertices; reason: a cycle is determined by its arc set, which is how it enters the incidence matrices; loops are not cycles, and tournaments have none
--   - encoding: the family F written in letters a, …, o → each string decoded letter by letter through the list E1 into a set of 1-based arc pairs, compared with the image of F under e ↦ (tail + 1, head + 1); reason: the same 41 arc sets; the map from arcs to pairs is injective
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, proof of Lemma 4.1, Claim 1, pp.24–25

import Mathlib
import Definitions.Def_FASTournament_Arc
import Definitions.Def_FASTournament_IsMinimalFAS
import Definitions.Def_FASTournament_G1

open Classical

namespace FASTournament

/-- **Claim 1 (proof of Lemma 4.1): the 41 minimal FASs of `G₁`.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, proof of Lemma 4.1, Claim 1, pp.24–25: "Let F be the family of all minimal feedback arc
sets of G1. Then |F| = 41 and F = {ehj, afhk, dgjo, …, beijmno}, where, for instance, ehj stands
for the minimal FAS consisting of arcs e, h and j."
The letters `a, b, …, o` denote the arcs `12, 23, 34, 45, 51, 13, 35, 52, 24, 41, 16, 26, 63, 64,
65` of `E1` in this order (p.24).

An arc set `F` of `G₁` is a minimal FAS iff, written with the 1-based vertex labels of p.24, it
is one of the 41 listed sets; and there are exactly 41 minimal FASs.

**Formalization Note.** An arc `e` of `G₁` (vertices `Fin 6`) is written as the pair
`(e.1.1 + 1, e.1.2 + 1)`; the letter `c` is decoded as the entry of `E1` at index
`c - 'a'`. -/
theorem claim_1 :
    (∀ F : Finset (Arc G1), IsMinimalFAS G1 F ↔
      F.image (fun e => (e.1.1.val + 1, e.1.2.val + 1)) ∈
        (["ehj", "afhk", "dgjo", "acehk", "acehn", "acghk", "bdejl", "beijl",
          "bfikl", "cehin", "cgikl", "cgino", "degjl", "dgjkl", "abdfkl", "acdgkl",
          "acdgko", "acdgno", "acghno", "adfgkl", "adfgko", "adghjk", "aefhmn", "afhmno",
          "bceikl", "bceiln", "bdejmo", "bdfjkl", "bdfjmo", "bfimno", "cegijl", "cegiln",
          "cehikl", "abdfkmo", "abdfmno", "adfgmno", "adfhjmo", "bceimno", "befhimn", "befilmn",
          "beijmno"].map
          (fun s : String => (s.toList.map (fun c : Char =>
            ([(1, 2), (2, 3), (3, 4), (4, 5), (5, 1), (1, 3), (3, 5), (5, 2), (2, 4), (4, 1),
              (1, 6), (2, 6), (6, 3), (6, 4), (6, 5)] : List (ℕ × ℕ)).getD
                (c.toNat - 'a'.toNat) (0, 0))).toFinset))) ∧
    Nat.card {F : Finset (Arc G1) // IsMinimalFAS G1 F} = 41 := by sorry

end FASTournament
