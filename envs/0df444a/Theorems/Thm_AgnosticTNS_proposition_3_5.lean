-- Prove2me | Theorems.Thm_AgnosticTNS_proposition_3_5
-- name    : AgnosticTNS.proposition_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:39:59.270427+00:00
-- url     : https://prove2.me/theorems/f8c9b90f-17cd-4766-9fbc-de291876311d
-- title:
--   Proposition 3.5 — overlap guarantee for the agnostic sequence learner
-- statement:
--   Let $\rho$ be an arbitrary $n$-qudit state with $\mathrm{OPT}_{G,\chi}(\rho)\ge\vartheta$, and let $\epsilon,\vartheta\in(0,1]$. Assume that every call to Sub-Tomography in Algorithm 1 succeeds with its requested trace-norm accuracy ($\gamma_i$ at compressing step $i$, $\gamma_{\mathrm{fin}}=\epsilon/8$ at the final call). Then the output state satisfies
--   $$
--   \langle\hat\psi|\rho|\hat\psi\rangle\ge\mathrm{OPT}_{G,\chi}(\rho)-\epsilon .
--   $$
--   Moreover, each postselection map $K$ used by the algorithm has success probability $\mathrm{tr}(K\rho K^\dagger)\ge\vartheta/2$.
--
--   The second clause makes the success-probability interval $[\vartheta/2,1]$ passed to every tomography call valid.
--
--   Differences from the source:
--   - encoding: vertices $[n]$, labels $[d]$, steps $[L]$ (1-based), vectors in $(\mathbb C^d)^{\otimes n}$ → `Fin n`, `Fin d`, `Fin L` (0-based), functions `(Fin n → Fin d) → ℂ`; reason: Lean convention; same instances
--   - encoding: standing assumptions $n\ge1$, $d\ge2$, $\epsilon\in(0,1]$, $\delta\in(0,1)$ of p.11 → explicit hypotheses; reason: the section's standing assumptions are binders
--   - encoding: Algorithm 1 (one execution, with its choices) → every admissible run (`Run.IsValid`) at the parameters $p_i,\Lambda_i$ of Section 3.2; reason: the algorithm makes choices ($R_i$, eigenvector spans, unitaries, top eigenvector); every choice is covered
--   - generalization: Sub-Tomography estimates are positive semidefinite of trace at most one → runs only need positive semidefinite estimates; reason: the class of runs is larger and contains every run of the paper's algorithm, so the statement specialises to the source's
--   - encoding: each postselection map used by the algorithm → $K_{<i}$ at every compressing step $i$ (line 10) and the final $K_c$ (line 20); reason: these are the maps passed to Sub-Tomography
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Proposition 3.5, Eqs. (3.30)–(3.31), p.21

import Mathlib
import Definitions.Def_AgnosticTNS_OPT
import Definitions.Def_AgnosticTNS_Run_IsValid
import Definitions.Def_AgnosticTNS_Run_IsAccurate
import Definitions.Def_AgnosticTNS_Run_psiHat
import Definitions.Def_AgnosticTNS_pP
import Definitions.Def_AgnosticTNS_LambdaP
import Definitions.Def_AgnosticTNS_gammaP
import Definitions.Def_WildeQIT_IsDensityOperator
open Matrix
open scoped ComplexOrder

namespace AgnosticTNS

/-- **Proposition 3.5 (Overlap guarantee for the agnostic sequence learner)**, pp.21–22 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). Let `ρ`
be an arbitrary `n`-qudit state with `OPT_{G,χ}(ρ) ≥ ϑ` (3.30), and assume that every Sub-Tomography
call in Algorithm 1 succeeds with its requested trace-norm accuracy. Then the output satisfies
`⟨ψ̂|ρ|ψ̂⟩ ≥ OPT_{G,χ}(ρ) − ϵ` (3.31), and each postselection map used by the algorithm has success
probability at least `ϑ/2`.

**Formalization Note** Every valid run (`Run.IsValid`) that is accurate (`Run.IsAccurate`:
`‖σ_i − σ̂_i‖₁ ≤ γ_i` at every compressing step and `‖τ − τ̂‖₁ ≤ γ_fin = ϵ/8`). The postselection maps
used are `K_{<i}` at every compressing step `i` (line 10) and the final `K_c` (line 20); success
probability is `tr(KρK†)`. -/
theorem proposition_3_5 {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) (G : SimpleGraph (Fin n)) (χ : ℕ)
    (hχ : 1 ≤ χ) (Ls : LearningSequence n) (ε ϑ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hϑ : 0 < ϑ)
    (hϑ1 : ϑ ≤ 1) (ρ : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) (hopt : ϑ ≤ OPT d G χ ρ) (run : Run d n Ls)
    (hrun : run.IsValid (pP d G χ Ls ε ϑ) (LambdaP G χ Ls ε ϑ))
    (hacc : run.IsAccurate (pP d G χ Ls ε ϑ) ρ (gammaP G χ Ls ε ϑ) (ε / 8)) :
    OPT d G χ ρ - ε ≤ expVal ρ (run.psiHat (pP d G χ Ls ε ϑ)) ∧
      (∀ i, pP d G χ Ls ε ϑ i < (Mset Ls run.R i).card →
        ϑ / 2 ≤ (run.Kupto (pP d G χ Ls ε ϑ) i.val * ρ *
          (run.Kupto (pP d G χ Ls ε ϑ) i.val)ᴴ).trace.re) ∧
      ϑ / 2 ≤ (run.Kupto (pP d G χ Ls ε ϑ) Ls.L * ρ * (run.Kupto (pP d G χ Ls ε ϑ) Ls.L)ᴴ).trace.re := by sorry

end AgnosticTNS
