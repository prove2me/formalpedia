-- Prove2me | Theorems.Thm_AgnosticTNS_lemma_3_4
-- name    : AgnosticTNS.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:38:40.147129+00:00
-- url     : https://prove2.me/theorems/4b31dd3d-3c26-4d2d-a9b1-fc416e3beab8
-- title:
--   Lemma 3.4 — rank invariant for reference TNSs
-- statement:
--   Let $|\phi\rangle\in S_d(G,\chi)$ and consider Algorithm 1 on a learning sequence of $G$, just before step $i$ is processed. Let $K_{<i}$ be the cumulative postselection map constructed so far (the product of the projections and compression unitaries of the earlier compressing steps). Then the vector $K_{<i}|\phi\rangle$, viewed across the bipartition
--   $$
--   M_i\ \big|\ [n]\setminus M_i,
--   $$
--   has Schmidt rank at most $r_i=\chi^{|\mathrm{cut}_G(S_i)|}$.
--
--   Earlier compressions never increase the Schmidt rank of a reference state across the cut relevant to the current step.
--
--   Differences from the source:
--   - encoding: vertices $[n]$, labels $[d]$, steps $[L]$ (1-based), vectors in $(\mathbb C^d)^{\otimes n}$ → `Fin n`, `Fin d`, `Fin L` (0-based), functions `(Fin n → Fin d) → ℂ`; reason: Lean convention; same instances
--   - encoding: standing assumptions $n\ge1$, $d\ge2$, $\epsilon\in(0,1]$, $\delta\in(0,1)$ of p.11 → explicit hypotheses; reason: the section's standing assumptions are binders
--   - encoding: Algorithm 1 (one execution, with its choices) → every admissible run (`Run.IsValid`) at the parameters $p_i,\Lambda_i$ of Section 3.2; reason: the algorithm makes choices ($R_i$, eigenvector spans, unitaries, top eigenvector); every choice is covered
--   - generalization: Sub-Tomography estimates are positive semidefinite of trace at most one → runs only need positive semidefinite estimates; reason: the class of runs is larger and contains every run of the paper's algorithm, so the statement specialises to the source's
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Lemma 3.4, Eq. (3.28), p.20

import Mathlib
import Definitions.Def_AgnosticTNS_TNSchi
import Definitions.Def_AgnosticTNS_schmidtRank
import Definitions.Def_AgnosticTNS_Run_IsValid
import Definitions.Def_AgnosticTNS_Run_Kupto
import Definitions.Def_AgnosticTNS_pP
import Definitions.Def_AgnosticTNS_LambdaP
open Matrix
open scoped ComplexOrder

namespace AgnosticTNS

/-- **Lemma 3.4 (Rank invariant for reference TNSs)**, p.20 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). Let `|ϕ⟩ ∈ S_d(G, χ)` and consider
Algorithm 1 just before step `i`, with `K_{<i}` the cumulative postselection map constructed so far
(the product over the earlier compressing steps). Then `K_{<i}|ϕ⟩` has Schmidt rank at most
`r_i = χ^{|cut_G(S_i)|}` across `M_i | [n] ∖ M_i` (3.28).

**Formalization Note** "Algorithm 1" is every valid run (`Run.IsValid`: every choice of `R_i`, `σ̂_i`,
`W_i`, `Ũ_i`, `φ̂` the algorithm allows), with the parameters `p_i, Λ_i` of §3.2 at `ε, ϑ ∈ (0, 1]`;
`K_{<i}` is `Run.Kupto run p i`. -/
theorem lemma_3_4 {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) (G : SimpleGraph (Fin n)) (χ : ℕ)
    (hχ : 1 ≤ χ) (Ls : LearningSequence n) (ε ϑ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hϑ : 0 < ϑ)
    (hϑ1 : ϑ ≤ 1) (φ : (Fin n → Fin d) → ℂ) (hφ : φ ∈ TNSchi d G χ) (run : Run d n Ls)
    (hrun : run.IsValid (pP d G χ Ls ε ϑ) (LambdaP G χ Ls ε ϑ)) (i : Fin Ls.L) :
    schmidtRank (Mset Ls run.R i) (run.Kupto (pP d G χ Ls ε ϑ) i.val *ᵥ φ) ≤ rr G χ Ls i := by sorry

end AgnosticTNS
