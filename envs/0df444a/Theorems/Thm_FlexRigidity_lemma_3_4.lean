-- Prove2me | Theorems.Thm_FlexRigidity_lemma_3_4
-- name    : FlexRigidity.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:21:25.977216+00:00
-- url     : https://prove2.me/theorems/f4c6a1ac-9b7b-4c41-b2e1-775585562959
-- title:
--   Lemma 3.4 — no regularization needed after a replacer
-- statement:
--   Let $1<\alpha<2$, $\mathcal E\in\mathrm{CPTP}(M,SQ)$, $\omega_S$ positive definite, and let $\mathcal P\in\mathrm{CP}(SQ,SQ)$ be the replacer map $X_{SQ}\mapsto\omega_S\otimes\operatorname{Tr}_SX_{SQ}$. Then for $\mathcal F=\mathcal P\circ\mathcal E$ and $R\cong M$,
--   $$D^{\mathrm{reg}}_\alpha(\mathcal E\otimes\mathrm{id}_R\|\mathcal F\otimes\mathrm{id}_R)\le D_{1/(2-\alpha)}(\mathcal E\otimes\mathrm{id}_R\|\mathcal F\otimes\mathrm{id}_R).$$
--   The channel divergences carry no stabilizer beyond the explicit $\mathrm{id}_R$ (Definition 2.10), and $D^{\mathrm{reg}}$ is the regularization of Definition 2.11. This removes the regularization from the chain rule of Lemma 3.5.
--
--   Differences from the source:
--   - encoding: reference register R ≅ M → the reference is the type M itself, placed before the system register; reason: Lean convention; the same register up to the identification
--   - encoding: divergences and channel divergences with values in [0, +∞] → values in EReal (extended reals); reason: Lean convention; the +∞ conventions of Definition 2.7 are kept, no instance changes
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Lemma 3.4, p. 24

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_regChanDiv
import Definitions.Def_FlexRigidity_replacer
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Lemma 3.4** (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444, artifact sha256
8c67699d…, p. 24). Let `1 < α < 2`, `E ∈ CPTP(M, SQ)`, `ω_S` positive definite, and
`P ∈ CP(SQ, SQ)` the replacer map that replaces `S` with `ω_S`. Then for `F = P ∘ E` and `R ≅ M`,
`D^reg_α(E ⊗ id_R‖F ⊗ id_R) ≤ D_{1/(2−α)}(E ⊗ id_R‖F ⊗ id_R)`.

**Formalization Note** `R ≅ M` is the type `M` itself, placed first (`idTensorSuperop`); the
channel divergences have no further stabilizer (Definition 2.10). -/
theorem lemma_3_4 {M S Q : Type} [Fintype M] [DecidableEq M] [Fintype S] [DecidableEq S]
    [Fintype Q] [DecidableEq Q] (α : ℝ) (hα : 1 < α ∧ α < 2) (E : Superop M (S × Q))
    (hE : IsChannel E) (ω : Matrix S S ℂ) (hω : ω.PosDef) :
    regChanDiv α (idTensorSuperop (R := M) E)
        (idTensorSuperop (R := M) (fun X => replacer (Q := Q) ω (E X))) ≤
      chanDiv (1 / (2 - α)) (idTensorSuperop (R := M) E)
        (idTensorSuperop (R := M) (fun X => replacer (Q := Q) ω (E X))) := by sorry

end FlexRigidity
