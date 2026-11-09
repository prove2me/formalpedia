-- Prove2me | Theorems.Thm_ChanTomoNB_lemma_4_3
-- name    : ChanTomoNB.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:33:37.665358+00:00
-- url     : https://prove2.me/theorems/4ed3f157-0e1b-4a73-ac5d-751b0043cb45
-- title:
--   Lemma 4.3 — $\Gamma_P\preceq(e+2en/(d'(d'+\alpha)))^{\alpha d'}\Gamma$
-- statement:
--   Let $d<D<2d$, $\alpha=D-d$ and $1\le d'\le d$. For an isometry $W_P:\mathbb C^{d'}\to\mathbb C^{d'+\alpha}$ with $W_PW_P^\dagger=P$, let $V_{P,U}=I_{d-d'}\oplus W_PU$ and
--   $$
--   \Gamma_P=\mathbb E_{U\sim\mathbb U_{d'}}C_{V_{P,U}}^{\otimes n},\qquad \Gamma=\mathbb E_{P\sim\mathrm{Proj}_{d'}(d'+\alpha)}\Gamma_P .
--   $$
--   Then
--   $$
--   \Gamma_P\preceq\Big(e+\frac{2en}{d'(d'+\alpha)}\Big)^{\alpha d'}\Gamma .
--   $$
--
--   The averaged Choi operator $\Gamma$ is a universal ($P$-independent) upper bound for every $\Gamma_P$, which caps the success of any discriminating tester.
--
--   Differences from the source:
--   - encoding: standing assumptions of §4: d < D < 2d, α = D − d, 1 ≤ d′ ≤ d (p.21) → D = d + α with hypotheses 0 < α < d, 1 ≤ d′ ≤ d; reason: the same parameters
--   - generalization: "we fix an isometry W_P" for P ∈ Proj_{d′}(d′+α) (p.21) → every isometry W_P : C^{d′} → C^{d′+α} (P = W_P W_P†); reason: every rank-d′ projector has such isometries, and the statement holds for each; it specializes to the fixed choice
--   - encoding: E_{U∼U_{d′}}, E_{P∼Proj_{d′}(d′+α)} of matrices → entrywise Bochner integrals against the normalized Haar measure; P ∼ Proj_{d′}(d′+α) is P = U′P0U′† with W_P = U′W0, U′ ∼ U_{d′+α} (p.24); reason: the same matrices
--   - encoding: C_E^{⊗n} on ⊗_j(H_{B,j} ⊗ H_{A,j}) and p_i = tr(T_i^T C_E^{⊗n}) (p.12) → a query is indexed Fin d1 × Fin d2 (input first), C_E^{⊗n} is reindexed to that order, and tr(T^T C) is the entrywise pairing ∑_{x,y} T_{xy} C_{xy}; reason: the same numbers
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, Lemma 4.3, Eq. (48), p.22

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_ChanTomoNB_Tester
import Definitions.Def_ChanTomoNB_Proj
import Definitions.Def_ChanTomoNB_isoDiscrimination

open Matrix MeasureTheory
open scoped ComplexOrder

namespace ChanTomoNB

/-- **Lemma 4.3.** Chen, Oufkir, *Quantum channel tomography: optimal bounds in the near-boundary
regime*, arXiv:2611.03639v1, Lemma 4.3, Eq. (48), p.22: "For Γ_P and Γ defined in Equation (46)
and Equation (47), we have Γ_P ⪯ (e + 2en/(d′(d′ + α)))^{αd′} Γ."

Here `Γ_P = E_{U∼U_{d′}} C_{V_{P,U}}^{⊗n}` (Eq. (46)), `Γ = E_{P∼Proj_{d′}(d′+α)} Γ_P` (Eq. (47)),
`V_{P,U} = I_{d−d′} ⊕ W_P U` (Eq. (45)). Under the standing assumptions of §4, for every `n` and
every isometry `W_P`, `(e + 2en/(d′(d′+α)))^{αd′} Γ − Γ_P ⪰ 0`.

**Formalization Note.** `D = d + α` (`0 < α < d` is `d < D < 2d`). `C_V` is the Choi operator of
`X ↦ V X V†`, and `C_V^{⊗n}` is written on the tester's space `⊗_j (ℂ^d ⊗ ℂ^D)` (`choiPow`), a
fixed permutation of tensor factors applied to both sides. Expectations are entrywise Bochner
integrals against the Haar probability measure. Every isometry `W_P` (Reading 7). -/
theorem lemma_4_3 (d d' α : ℕ) (hα : 0 < α) (hαd : α < d) (hd' : 1 ≤ d') (hd'd : d' ≤ d)
    (n : ℕ) (Wp : Matrix (Fin (d' + α)) (Fin d') ℂ) (hW : Wpᴴ * Wp = 1) :
    ((((Real.exp 1 + 2 * Real.exp 1 * n / ((d' : ℝ) * ((d' : ℝ) + α))) ^ (α * d') : ℝ) : ℂ) •
        Gamma (d - d') d' α n - GammaP (d0 := d - d') n Wp).PosSemidef := by sorry

end ChanTomoNB
