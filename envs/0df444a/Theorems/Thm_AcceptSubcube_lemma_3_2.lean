-- Prove2me | Theorems.Thm_AcceptSubcube_lemma_3_2
-- name    : AcceptSubcube.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:04.126522+00:00
-- url     : https://prove2.me/theorems/98692224-d9c1-4278-84d7-7741e523606d
-- title:
--   Lemma 3.2 — canonical bounded-outdegree orientation of the one-inclusion graph
-- statement:
--   1. For every finite index set $T$, every family $F\subseteq\{0,1\}^T$ and every $v$ with $\mathrm{VCdim}(F)\le v$, the one-inclusion graph of $F$ has an orientation of maximum outdegree at most $v$.
--   2. There is a deterministic polynomial-time orientation rule which, given the labelled coordinate set $T$ and $F$ explicitly, returns an orientation of the one-inclusion graph of $F$ of maximum outdegree at most $\mathrm{VCdim}(F)$, for every $T$ and $F$. Being a function of $(T,F)$, its output depends only on the labelled coordinate set and on $F$.
--
--   The second clause is what the recovery procedure of Lemma 3.3 needs: the orientation is fixed before any coordinate is withheld.
--
--   Differences from the source:
--   - generalization: F ⊆ {0,1}^T for the coordinate set T → F a finite family of functions from any finite type ι to Bool (clause 1); reason: ι = T specializes to the source
--   - reading: such an orientation (outdegree ≤ v when VCdim(F) ≤ v) computed in polynomial time by a deterministic procedure depending only on T and F → a TM2 polynomial-time map (T, F) ↦ list of directed edges whose output is an orientation of maximum outdegree ≤ VCdim(F), for all T, F; reason: "≤ v whenever VCdim ≤ v" for every v is the bound VCdim(F); a function of (T, F) depends only on them
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Lemma 3.2, p.12

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_AcceptSubcube_FK
import Definitions.Def_AcceptSubcube_GoodOrient
import Definitions.Def_AcceptSubcube_encInst

namespace AcceptSubcube

/-- **Lemma 3.2 (Canonical bounded-outdegree orientation).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Lemma 3.2, p.12: "If VCdim(F) ≤ v, the
one-inclusion graph of F has an orientation of maximum outdegree at most v. Given F explicitly, such
an orientation can be computed in polynomial time by a deterministic procedure whose output depends
only on the labeled coordinate set T and on F."

(1) For every finite family `F ⊆ {0,1}^ι` with `VCdim(F) ≤ v` there is an orientation of maximum
outdegree `≤ v`. (2) There is a deterministic polynomial-time map `orient` from `(T, F)` (labels and
explicit family) to an orientation, which is an orientation of maximum outdegree at most `VCdim(F)`
(hence `≤ v` whenever `VCdim(F) ≤ v`) for every `T`, `F` (`GoodOrient`).

**Formalization Note.** VC dimension is Mathlib's `Finset.vcDim` of the family as a set family.
Being a function of `(T, F)`, `orient`'s output depends only on them. -/
theorem lemma_3_2 :
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : Finset (ι → Bool)) (v : ℕ),
        (toSets F).vcDim ≤ v →
        ∃ O : (ι → Bool) → ι → Bool, IsOrientation F O ∧ ∀ y ∈ F, outdeg F O y ≤ v) ∧
    (∃ orient : List ℕ × List (List Bool) → List (List Bool × ℕ),
        Nonempty (Turing.TM2ComputableInPolyTime encTF encOrient orient) ∧ GoodOrient orient) := by sorry

end AcceptSubcube
