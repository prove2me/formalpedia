-- Prove2me | Theorems.Thm_ChanTomoNB_theorem_4_2
-- name    : ChanTomoNB.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:33:30.767196+00:00
-- url     : https://prove2.me/theorems/c33ab880-bf05-4c91-a298-fdaa57f28190
-- title:
--   Theorem 4.2 — hardness of discrimination: $\mathbb P[\mathrm{success}]\le|\mathcal N|^{-1}(e+2en/(d'(d'+\alpha)))^{\alpha d'}$
-- statement:
--   Let $d<D<2d$, $\alpha=D-d$ and $1\le d'\le d$. Let $\mathcal N\subseteq\mathrm{Proj}_{d'}(d'+\alpha)$ be a nonempty finite set and $P\mapsto W_P$ a choice of isometries with $W_PW_P^\dagger=P$. In Problem 4.1 the referee draws $P\in\mathcal N$ uniformly and an independent Haar $U\sim\mathbb U_{d'}$, and provides queries to $V_{P,U}=I_{d-d'}\oplus W_PU$; the task is to identify $P$. The success probability of any $n$-query algorithm satisfies
--   $$
--   \mathbb P[\mathrm{success}]\le\frac1{|\mathcal N|}\Big(e+\frac{2en}{d'(d'+\alpha)}\Big)^{\alpha d'} .
--   $$
--
--   With fewer than about $d'(d'+\alpha)$ queries, no learner identifies the hidden range much better than guessing.
--
--   Differences from the source:
--   - encoding: standing assumptions of §4: d < D < 2d, α = D − d, 1 ≤ d′ ≤ d (p.21) → D = d + α with hypotheses 0 < α < d, 1 ≤ d′ ≤ d; reason: the same parameters
--   - reading: an algorithm with query access that may use a reference system, quantum memory and adaptive inputs (pp.10, 12) → every tester with n queries (Definition 2.3): PSD operators T_i whose sum is a quantum (n+1)-comb; reason: the paper proves its lower bounds in the tester model and states that every sequential, adaptive, coherent algorithm is a tester (p.12); quantifying over all testers is the stronger reading
--   - generalization: a tester {T_i}_i → an arbitrary outcome type ι with ∑_i T_i converging entrywise (HasSum); reason: every finite tester is the case of a finite ι
--   - generalization: a tester {T_P}_{P∈N} whose outcome is the guess → a tester with arbitrary outcomes and an arbitrary guess map g from outcomes to matrices; success is g(i) = P; reason: a tester {T_P}_{P∈N} is the case of outcomes N and g = id
--   - generalization: "we fix an isometry W_P" for P ∈ Proj_{d′}(d′+α) (p.21) → every isometry W_P : C^{d′} → C^{d′+α} (P = W_P W_P†); reason: every rank-d′ projector has such isometries, and the statement holds for each; it specializes to the fixed choice
--   - encoding: N ⊆ Proj_{d′}(d′+α) finite, P drawn uniformly → N a nonempty Finset of rank-d′ projectors; reason: a uniform draw needs N ≠ ∅
--   - encoding: E_{U∼U_{d′}}, E_{P∼Proj_{d′}(d′+α)} of matrices → entrywise Bochner integrals against the normalized Haar measure; P ∼ Proj_{d′}(d′+α) is P = U′P0U′† with W_P = U′W0, U′ ∼ U_{d′+α} (p.24); reason: the same matrices
--   - encoding: C_E^{⊗n} on ⊗_j(H_{B,j} ⊗ H_{A,j}) and p_i = tr(T_i^T C_E^{⊗n}) (p.12) → a query is indexed Fin d1 × Fin d2 (input first), C_E^{⊗n} is reindexed to that order, and tr(T^T C) is the entrywise pairing ∑_{x,y} T_{xy} C_{xy}; reason: the same numbers
--   - encoding: queries to the isometry V_{P,U} (p.21) → the tester applied to the isometry channel X ↦ V_{P,U} X V_{P,U}†, whose Choi operator is |V_{P,U}⟩⟩⟨⟨V_{P,U}| (p.22); P[success] = |N|^{-1} ∑_{P∈N} ∑_i [g(i) = P] E_U p_i(V_{P,U}); reason: the paper's own expression of the success probability (proof of Theorem 4.2, p.22)
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, Theorem 4.2, p.22; Problem 4.1, p.21

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_ChanTomoNB_Tester
import Definitions.Def_ChanTomoNB_Proj
import Definitions.Def_ChanTomoNB_isoDiscrimination

open Matrix MeasureTheory
open scoped ComplexOrder

namespace ChanTomoNB

/-- **Theorem 4.2 (Hardness of discrimination).** Chen, Oufkir, *Quantum channel tomography:
optimal bounds in the near-boundary regime*, arXiv:2611.03639v1, Theorem 4.2, p.22: "The success
probability of any n-query algorithm for Problem 4.1 is bounded as
P[success] ≤ (1/|N|)(e + 2en/(d′(d′ + α)))^{αd′}."

Problem 4.1 (p.21): "Suppose N ⊆ Proj_{d′}(d′ + α) is a given finite set of orthogonal
projectors. The referee draws a projector P ∈ N uniformly, and also independently draws a
Haar-random U ∼ U_{d′} and provides you queries to the isometry V_{P,U}. The task for you is to
identify P." Under the standing assumptions of §4, for every nonempty finite set `N` of rank-`d′`
projectors on `ℂ^{d′+α}`, every choice `P ↦ W_P` of isometries with `W_P W_P† = P`, every
`n`-query tester on `(ℂ^d, ℂ^D)` and every guess map `g` from its outcomes, the success
probability is at most `(1/|N|)(e + 2en/(d′(d′+α)))^{αd′}`.

**Formalization Note.** An `n`-query algorithm is a tester (Definition 2.3, Reading 1) with an
arbitrary outcome type (Reading 2) and a guess `g i` on outcome `i`; a tester `{T_P}_{P∈N}` is the
case `g = id`. `ℂ^d = ℂ^{d−d′} ⊕ ℂ^{d′}`, `ℂ^D = ℂ^{d−d′} ⊕ ℂ^{d′+α}` as in Eq. (45), `D = d + α`.
`N` is nonempty, as "draws a projector P ∈ N uniformly" requires. -/
theorem theorem_4_2 (d d' α : ℕ) (hα : 0 < α) (hαd : α < d) (hd' : 1 ≤ d') (hd'd : d' ≤ d)
    (n : ℕ) (T : Tester (Fin (d - d') ⊕ Fin d') (Fin (d - d') ⊕ Fin (d' + α)) n)
    (N : Finset (Matrix (Fin (d' + α)) (Fin (d' + α)) ℂ)) (hN : N.Nonempty)
    (hNP : ∀ P ∈ N, P ∈ Proj d' (Fin (d' + α)))
    (W : Matrix (Fin (d' + α)) (Fin (d' + α)) ℂ → Matrix (Fin (d' + α)) (Fin d') ℂ)
    (hW : ∀ P ∈ Proj d' (Fin (d' + α)), (W P)ᴴ * W P = 1 ∧ W P * (W P)ᴴ = P)
    (g : T.ι → Matrix (Fin (d' + α)) (Fin (d' + α)) ℂ) :
    discrimSuccess T N W g ≤
      1 / (N.card : ℝ) * (Real.exp 1 + 2 * Real.exp 1 * n / ((d' : ℝ) * ((d' : ℝ) + α))) ^ (α * d') := by sorry

end ChanTomoNB
