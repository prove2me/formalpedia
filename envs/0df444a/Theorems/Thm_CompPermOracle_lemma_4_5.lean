-- Prove2me | Theorems.Thm_CompPermOracle_lemma_4_5
-- name    : CompPermOracle.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:09.865229+00:00
-- url     : https://prove2.me/theorems/2d8524c4-64de-4484-bb6d-4f737f3d6544
-- title:
--   Lemma 4.5 — bandedness: queries change the level by at most one
-- statement:
--   For all $x,y\in[N]$ and every $r$,
--   $$
--   Q_{x,y}\mathcal H_r\subseteq\mathcal H_{r-1}\oplus\mathcal H_r\oplus\mathcal H_{r+1},\qquad M_{x,y}\mathcal L_r\subseteq\mathcal L_{r-1}\oplus\mathcal L_r\oplus\mathcal L_{r+1}.
--   $$
--   Both hold for inverse queries: the inverse purified query uses the same projectors $Q_{x,y}$, and on $\mathcal L$ the inverse operator is $FM_{y,x}F$. Hence a purified computation beginning in $\mathcal H_0$ is supported on $\mathcal H_{\le q}$ after $q$ queries.
--
--   This locality in the level is what allows one-query bounds on $\mathcal H_{\le t}$ to be chained.
--
--   Differences from the source:
--   - generalization: a purified computation with forward and inverse queries → oracle steps coherently controlled on a direction bit, in the last clause; reason: a fixed schedule is the case where the algorithm sets the bit classically
--   - reading: a purified computation beginning in $\mathcal H_0$ → the purified experiment of the query model, starting in $\mathrm{init}\otimes|S_N\rangle$; reason: $\mathcal H_0$ is spanned by $|S_N\rangle$, so every start in (accessible) $\otimes\mathcal H_0$ has this form
--   - encoding: $\mathcal H_{r-1}$, $\mathcal L_{r-1}$ at $r=0$; $\oplus$; support on $\mathcal H_{\le q}$ → the subspace $0$; supremum of subspaces; every slice of the joint state on the accessible registers lies in $\mathcal H_{\le q}$; reason: the same subspaces, as levels are orthogonal
--   - encoding: $[N]=\{1,\dots,N\}$, blank symbol $\bot$ → `Fin N` (0-based), $\bot$ = `none`; reason: a relabelling; no index appears in the bound
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Lemma 4.5, p.13

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_CompPermOracle_Levels
import Definitions.Def_CompPermOracle_Alg

namespace CompPermOracle

/-- Lemma 4.5, Bandedness (Carolan, Majenz, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), p.13). The four clauses are: eq. (16) for `Q_{x,y}`;
the same for `M_{x,y}` on `ℒ`; the inverse-query version on `ℒ`; and the final sentence, that a purified
computation beginning in `ℋ_0` is supported on `ℋ_{≤q}` after `q` queries.

**Formalization Note.** Levels `r − 1` at `r = 0` are read as `0`. The inverse query `P⁻¹_y` of
Definition 3.2 uses the same projectors `Q_{x,y}`, so the first clause, for all `x, y`, is also its
inverse-query version. The inverse-query operator on `ℒ` is `F M_{y,x} F`, by Definition 3.6. A joint
state lies in `ℋ(Acc) ⊗ ℋ_{≤j}` exactly when each `regSlice` lies in `ℋ_{≤j}`. -/
theorem lemma_4_5 {N : ℕ} :
    (∀ (x y : Fin N) (r : ℕ), ∀ ψ ∈ Hlevel N r,
      assertP x y ψ ∈ HlevelBelow N r ⊔ Hlevel N r ⊔ Hlevel N (r + 1)) ∧
    (∀ (x y : Fin N) (r : ℕ), ∀ a ∈ Lsub N r,
      compM x y a ∈ LsubBelow N r ⊔ Lsub N r ⊔ Lsub N (r + 1)) ∧
    (∀ (x y : Fin N) (r : ℕ), ∀ a ∈ Lsub N r,
      flipL (compM y x (flipL a)) ∈ LsubBelow N r ⊔ Lsub N r ⊔ Lsub N (r + 1)) ∧
    (∀ (W : Type) [Fintype W] [DecidableEq W] (A : Alg N W) (j : ℕ) (c : Acc N W),
      regSlice (purifiedState A j) c ∈ Hle N j) := by sorry

end CompPermOracle
