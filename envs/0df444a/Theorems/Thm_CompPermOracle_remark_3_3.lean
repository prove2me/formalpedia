-- Prove2me | Theorems.Thm_CompPermOracle_remark_3_3
-- name    : CompPermOracle.remark_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:46.733266+00:00
-- url     : https://prove2.me/theorems/42a1fef5-7ec4-478f-a273-3537faa85a5f
-- title:
--   Remark 3.3 — tracing out the permutation memory recovers the random permutation experiment
-- statement:
--   Run a query algorithm $A$ in the purified experiment: the permutation register starts in $|S_N\rangle$, and each oracle step is the purified query $P$ or $P^{-1}$. Let $\psi_j$ be its state after $j$ queries. Let $\psi^\varphi_j$ be the state of $A$ after $j$ queries to $\tilde O_\varphi,\tilde O_{\varphi^{-1}}$. For all $j$ and all accessible basis states $c,c'$,
--   $$
--   \sum_{\varphi}\psi_j(c,\varphi)\overline{\psi_j(c',\varphi)}=\frac{1}{N!}\sum_{\varphi}\psi^\varphi_j(c)\overline{\psi^\varphi_j(c')}.
--   $$
--   So the reduced state on the accessible registers is the one obtained with a uniformly random, classically sampled permutation. This allows the analysis to work with a pure global state.
--
--   Differences from the source:
--   - generalization: swap queries $\tilde O_\varphi$, $\tilde O_{\varphi^{-1}}$ replaced by $P$, $P^{-1}$ → oracle steps coherently controlled on a direction bit; reason: a fixed schedule is the case where the algorithm sets the bit classically
--   - reading: tracing out the permutation memory after any interaction recovers the experiment → entrywise equality of the reduced density matrix and the $\varphi$-average of $|\psi^\varphi_j\rangle\langle\psi^\varphi_j|$, for every number $j$ of queries; reason: that is what the equality of two quantum experiments on the accessible registers says
--   - encoding: $[N]=\{1,\dots,N\}$, blank symbol $\bot$ → `Fin N` (0-based), $\bot$ = `none`; reason: a relabelling; no index appears in the bound
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Remark 3.3, p.6

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_CompPermOracle_Levels
import Definitions.Def_CompPermOracle_Alg

namespace CompPermOracle

/-- Remark 3.3 (Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), p.6):
tracing out the permutation memory of the purified experiment after any interaction recovers the
experiment with a uniformly random, classically sampled permutation.

**Formalization Note.** "After any interaction" is every number `j` of queries of every algorithm of
the goal's model. The traced-out state is the reduced density matrix on the accessible registers,
written entry by entry: `ρ(c, c') = ∑_φ ψ(c, φ) conj(ψ(c', φ))`. -/
theorem remark_3_3 {N : ℕ} {W : Type} [Fintype W] [DecidableEq W] (A : Alg N W) (j : ℕ)
    (c c' : Acc N W) :
    ∑ φ : Equiv.Perm (Fin N), purifiedState A j (c, φ) * star (purifiedState A j (c', φ)) =
      ((N.factorial : ℂ))⁻¹ *
        ∑ φ : Equiv.Perm (Fin N), realState A φ j c * star (realState A φ j c') := by sorry

end CompPermOracle
