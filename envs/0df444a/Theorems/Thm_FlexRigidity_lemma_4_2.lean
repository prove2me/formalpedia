-- Prove2me | Theorems.Thm_FlexRigidity_lemma_4_2
-- name    : FlexRigidity.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:21:32.375637+00:00
-- url     : https://prove2.me/theorems/a097e1b9-97d8-48bf-957e-c3d1773451bb
-- title:
--   Lemma 4.2 — duality relation for $\mathrm{CompExp}_\alpha$
-- statement:
--   Under Postulate Set 4.1, for every $\alpha>1$,
--   $$\mathrm{CompExp}_\alpha(\mathcal G,\mathcal P\circ\mathcal G;S_\Omega)=\inf_f\Big\{\sum_{i=1}^nR_{\alpha,\mathcal G_i,\mathcal P_i\circ\mathcal G_i}(f)+n\sup_{Q\in S_\Omega}\sum_cQ(c)f(c)\Big\},$$
--   the infimum over all real functions $f$ on $C$, with the conventions of (19). The left side is the penalized comparison exponent (19), the right side uses the stabilized round divergences (18). It turns the exponent obtained from the chain rule into the comparison exponent in Theorem 4.4.
--
--   Differences from the source:
--   - encoding: R_i with |R_i| ≥ |M_i| → R_i ≅ M_i in (18) and (19); reason: by Lemma 4.3(i) the values do not depend on the choice
--   - encoding: divergences and channel divergences with values in [0, +∞] → values in EReal (extended reals); reason: Lean convention; the +∞ conventions of Definition 2.7 are kept, no instance changes
--   - reading: T_i "only uses C_i as a control register" (Postulate 4.1(i)) → T_i maps every operator supported on the block C_i = c to an operator supported on the output block C_i = c; reason: the property the proof uses (p. 29, "Since T_i preserves C_i"); every T_i that uses C_i as a control register has it
--   - encoding: P_i of the form (16), specified on Z_i-classical inputs → ctrlReplacer, which pinches Z_i first and then acts as (16); reason: G_i has classical output Z_i, so P_i ∘ G_i and F_i are unchanged
--   - encoding: rounds i = 1, …, n with registers of varying dimension → families indexed by all i ∈ ℕ (Lean rounds 0, …, n−1), of which the statement uses the first n; registers are finite types; reason: Lean convention; data for later rounds are never used, and every finite family extends
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Lemma 4.2, eq. (20), p. 29

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_compExp
import Definitions.Def_FlexRigidity_Rterm
import Definitions.Def_FlexRigidity_IsAcceptSet
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Lemma 4.2 (Duality relation for `CompExp_α`)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 29). Under Postulate Set 4.1, for every `α > 1`,
`CompExp_α(G, P∘G; S_Ω) = inf_f { Σ_{i=1}^n R_{α,G_i,P_i∘G_i}(f) + n sup_{Q∈S_Ω} Σ_c Q(c) f(c) }` (20),
with the same convention for the sums as in (19); `f` ranges over all real functions on `C`.

**Formalization Note** The equality is in `EReal`; the inner supremum is an `EReal` `sSup`. -/
theorem lemma_4_2 {C : Type} {O M Z S J : ℕ → Type} [Fintype C] [DecidableEq C]
    [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]
    [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)] [∀ k, Fintype (Z k)] [∀ k, DecidableEq (Z k)]
    [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)] [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    (D : SeqData C O M Z S J) (n : ℕ) (hD : D.IsPostulate41 n) (SΩ : Set (C → ℝ))
    (hS : IsAcceptSet SΩ) (α : ℝ) (hα : 1 < α) :
    compExp D n α SΩ = ⨅ f : C → ℝ, (∑ i : Fin n, Rterm D i α f +
      (n : EReal) * sSup {v : EReal | ∃ Q ∈ SΩ, v = ((∑ c, Q c * f c : ℝ) : EReal)}) := by sorry

end FlexRigidity
