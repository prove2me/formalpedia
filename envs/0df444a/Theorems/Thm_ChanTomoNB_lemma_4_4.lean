-- Prove2me | Theorems.Thm_ChanTomoNB_lemma_4_4
-- name    : ChanTomoNB.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:33:38.426358+00:00
-- url     : https://prove2.me/theorems/4dd1fc86-d1a2-4f4e-b50b-cdd77c906fc3
-- title:
--   Lemma 4.4 — $X_{P,\ell}\preceq(e+2e\ell/(d'(d'+\alpha)))^{\alpha d'}X_\ell$
-- statement:
--   Let $d<D<2d$, $\alpha=D-d$ and $1\le d'\le d$. For $\ell\ge0$ and an isometry $W_P:\mathbb C^{d'}\to\mathbb C^{d'+\alpha}$ with $W_PW_P^\dagger=P$, let
--   $$
--   X_{P,\ell}=\mathbb E_{U\sim\mathbb U_{d'}}|W_PU\rangle\!\rangle\langle\!\langle W_PU|^{\otimes\ell},\qquad X_\ell=\mathbb E_{P\sim\mathrm{Proj}_{d'}(d'+\alpha)}X_{P,\ell}.
--   $$
--   Then
--   $$
--   X_{P,\ell}\preceq\Big(e+\frac{2e\ell}{d'(d'+\alpha)}\Big)^{\alpha d'}X_\ell .
--   $$
--
--   The masked moment for one range is dominated by the average over ranges, with a factor that stays bounded while $\ell\lesssim d'(d'+\alpha)$.
--
--   Differences from the source:
--   - encoding: standing assumptions of §4: d < D < 2d, α = D − d, 1 ≤ d′ ≤ d (p.21) → D = d + α with hypotheses 0 < α < d, 1 ≤ d′ ≤ d; reason: the same parameters
--   - generalization: "we fix an isometry W_P" for P ∈ Proj_{d′}(d′+α) (p.21) → every isometry W_P : C^{d′} → C^{d′+α} (P = W_P W_P†); reason: every rank-d′ projector has such isometries, and the statement holds for each; it specializes to the fixed choice
--   - encoding: E_{U∼U_{d′}}, E_{P∼Proj_{d′}(d′+α)} of matrices → entrywise Bochner integrals against the normalized Haar measure; P ∼ Proj_{d′}(d′+α) is P = U′P0U′† with W_P = U′W0, U′ ∼ U_{d′+α} (p.24); reason: the same matrices
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, Lemma 4.4, p.23

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_ChanTomoNB_Tester
import Definitions.Def_ChanTomoNB_Proj
import Definitions.Def_ChanTomoNB_isoDiscrimination

open Matrix MeasureTheory
open scoped ComplexOrder

namespace ChanTomoNB

/-- **Lemma 4.4.** Chen, Oufkir, *Quantum channel tomography: optimal bounds in the near-boundary
regime*, arXiv:2611.03639v1, Lemma 4.4, p.23: "For ℓ ≥ 0, let
X_{P,ℓ} = E_{U∼U_{d′}} |W_P U⟩⟩⟨⟨W_P U|^{⊗ℓ}, X_ℓ = E_{P∼Proj_{d′}(d′+α)} X_{P,ℓ}. Then,
X_{P,ℓ} ⪯ (e + 2eℓ/(d′(d′ + α)))^{αd′} X_ℓ."

Under the standing assumptions of §4 (`d < D < 2d`, `α = D − d`, `1 ≤ d′ ≤ d`), for every `ℓ` and
every isometry `W_P : ℂ^{d′} → ℂ^{d′+α}` (so `P = W_P W_P†` is a rank-`d′` projector),
`(e + 2eℓ/(d′(d′+α)))^{αd′} X_ℓ − X_{P,ℓ} ⪰ 0`.

**Formalization Note.** `D = d + α`, so `d < D < 2d` is `0 < α < d`. The expectations are
entrywise Bochner integrals against `QAlgorithms.Schur.unitaryHaar`; `P ∼ Proj_{d′}(d′+α)` is
`P = U′P₀U′†` with `W_P = U′W₀`, `U′ ∼ U_{d′+α}` (p.24); `X_{P,ℓ}` depends only on `P`. "We fix an
isometry W_P" is read as every isometry (Reading 7). `|X⟩⟩⟨⟨X|^{⊗ℓ}` is indexed by
`Fin ℓ → Fin (d′+α) × Fin d′`. -/
theorem lemma_4_4 (d d' α : ℕ) (hα : 0 < α) (hαd : α < d) (hd' : 1 ≤ d') (hd'd : d' ≤ d)
    (ℓ : ℕ) (Wp : Matrix (Fin (d' + α)) (Fin d') ℂ) (hW : Wpᴴ * Wp = 1) :
    ((((Real.exp 1 + 2 * Real.exp 1 * ℓ / ((d' : ℝ) * ((d' : ℝ) + α))) ^ (α * d') : ℝ) : ℂ) •
        Xl d' α ℓ - XP ℓ Wp).PosSemidef := by sorry

end ChanTomoNB
