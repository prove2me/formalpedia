-- Prove2me | Theorems.Thm_ChanTomoNB_lemma_5_3
-- name    : ChanTomoNB.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:30:37.073174+00:00
-- url     : https://prove2.me/theorems/c8b4a4a7-4622-4a40-898a-b77f46aa9fbd
-- title:
--   Lemma 5.3 — $\mathcal G$ is compact, $\mu(\mathcal G)\ge1/2$, and $\chi/(16C_0)\le\lambda_0\alpha^2/\kappa\le\chi/(2C_0)$
-- statement:
--   In the near-boundary regime ($d_2\ge2$, $r\ge1$, $d_1<rd_2<2d_1$), let $F$ be a balanced reference, $\Pi=I-FF^\dagger$, and
--   $$
--   \mathcal G=\{P\in\mathrm{Proj}_{d'}(\operatorname{im}\Pi):\operatorname{tr}_B(\Pi-P)\preceq\kappa I_r\},\qquad \kappa=C_0\Big(\frac\alpha r+\frac1{d_2}\Big),\ C_0=450 .
--   $$
--   Then
--
--   1. $\mathcal G$ is compact;
--   2. $\mu(\mathcal G)\ge1/2$, where $\mu$ is the invariant probability measure on $\mathrm{Proj}_{d'}(\operatorname{im}\Pi)$;
--   3. with $\alpha=rd_2-d_1$, $\chi=\min\{\alpha d_1,\alpha^2d_2^2\}$ and $\lambda_0=(d_1-d')/(2r)$,
--   $$
--   \frac{\chi}{16C_0}\le\frac{\lambda_0\alpha^2}{\kappa}\le\frac{\chi}{2C_0} .
--   $$
--
--   At least half of the signal ranges are balanced, which is what the packing argument needs.
--
--   Differences from the source:
--   - encoding: standing assumptions of §5: d2 ≥ 2 (p.10, "throughout"), r ≥ 1 and d1 < rd2 < 2d1 (p.24, "This construction applies throughout the near-boundary regime") → explicit hypotheses 2 ≤ d2, 1 ≤ r, d1 < r·d2, r·d2 < 2·d1; reason: the result is stated under the section's standing assumptions
--   - generalization: "Fix such an isometry F", "fix an isometry W_P", "a fixed projector" (pp.25–26) → every isometry F with tr_B(FF†) ⪰ λ0 I_r, every choice P ↦ W_P with W_P†W_P = I and W_P W_P† = P, and (for µ) every isometry Ψ onto im Π; reason: the statement holds for every admissible choice and specializes to the paper's fixed ones
--   - encoding: µ, the invariant probability measure on Proj_{d′}(im Π), obtained by conjugating a fixed projector by a Haar unitary (p.26) → µ(S) = Haar probability of {U ∈ U(d′+α) : Ψ U P0 U† Ψ† ∈ S}, P0 = diag(I_{d′}, 0_α); reason: the pushforward law, evaluated on the closed sets used here
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, Lemma 5.3, Eq. (53), p.26 (restated as Lemma 5.6, p.28)

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_ChanTomoNB_choiDist
import Definitions.Def_ChanTomoNB_diamondDist
import Definitions.Def_ChanTomoNB_matrixNorms
import Definitions.Def_ChanTomoNB_hardChannel

open Matrix MeasureTheory
open scoped ComplexOrder

namespace ChanTomoNB

/-- **Lemma 5.3 (Balanced Haar signals).** Chen, Oufkir, *Quantum channel tomography: optimal
bounds in the near-boundary regime*, arXiv:2611.03639v1, Lemma 5.3, p.26 (restated as Lemma 5.6,
p.28): "The set G is compact, µ(G) ≥ 1/2, and χ/(16C0) ≤ λ0α²/κ ≤ χ/(2C0)." (Eq. (53))

In the near-boundary regime, for every balanced reference `F`: the good set
`G = {P ∈ Proj_{d′}(im Π) : tr_B(Π − P) ⪯ κ I_r}` is compact; `µ(G) ≥ 1/2` for the invariant law
`µ` of `Proj_{d′}(im Π)` (built from any isometry `Ψ` onto `im Π`); and
`χ/(16 C₀) ≤ λ₀ α²/κ ≤ χ/(2 C₀)`, with `α = r d2 − d1`, `χ = min{α d1, α² d2²}`,
`λ₀ = (d1 − d′)/(2r)`, `κ = C₀(α/r + 1/d2)`, `C₀ = 450`.

**Formalization Note.** `µ(S)` is the Haar probability of `{U ∈ U(d′+α) : Ψ U P₀ U† Ψ† ∈ S}`
(`muProj`). "A fixed projector" is read as every projector `Ψ P₀ Ψ†`, `Ψ` any isometry onto
`im Π` (Reading 7). Compactness is in the standard topology of matrices. -/
theorem lemma_5_3 (d1 d2 r : ℕ) (hd2 : 2 ≤ d2) (hr : 1 ≤ r) (hlo : d1 < r * d2)
    (hhi : r * d2 < 2 * d1)
    (F : Matrix (Fin d2 × Fin r) (Fin (d1 - dp d1)) ℂ) (hF : IsBalancedRef d1 d2 r F) :
    IsCompact (goodSet (d1 := d1) F) ∧
      (∀ Ψ : Matrix (Fin d2 × Fin r) (Fin (dp d1 + alpha d1 d2 r)) ℂ,
        IsOuterIsometry (d1 := d1) F Ψ → (1 / 2 : ENNReal) ≤ muProj (d1 := d1) Ψ (goodSet (d1 := d1) F)) ∧
      chi d1 d2 r / (16 * C0) ≤ lam0 d1 r * (alpha d1 d2 r : ℝ) ^ 2 / kappa d1 d2 r ∧
      lam0 d1 r * (alpha d1 d2 r : ℝ) ^ 2 / kappa d1 d2 r ≤ chi d1 d2 r / (2 * C0) := by sorry

end ChanTomoNB
