-- Prove2me | Theorems.Thm_FRouting_fact_3_3
-- name    : FRouting.fact_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:09:06.248034+00:00
-- url     : https://prove2.me/theorems/6851a24f-89ec-4a92-8cb3-44126accbfb2
-- title:
--   Fact 3.3 — data processing for the fidelity
-- statement:
--   For density matrices $\rho,\sigma$ and any quantum channel $\mathcal E$,
--   $$F(\mathcal E(\rho),\mathcal E(\sigma))\ge F(\rho,\sigma).$$
--
--   The partial trace is an instance, and so is $\mathrm{id}\otimes$ a channel.
--
--   Differences from the source: none.
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Fact 3.3, p.14

import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_fidelity

set_option autoImplicit false

namespace FRouting

open WildeQIT

/-- **Fact 3.3 (data processing for the fidelity).** Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Fact 3.3, p.14: "The Fidelity of two states
is nondecreasing under any quantum channel ℰ: F(ℰ(ρ), ℰ(σ)) ≥ F(ρ, σ)."

**Formalization Note** `F` is the root fidelity. The channel is in Kraus form, between any finite
systems; the partial trace is an instance. -/
theorem fact_3_3 {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (E : QChannel a b) (ρ σ : Matrix a a ℂ) (hρ : PeresTerno.IsDensityMatrix ρ)
    (hσ : PeresTerno.IsDensityMatrix σ) :
    rootFidelity ρ σ ≤ rootFidelity (E.apply ρ) (E.apply σ) := by sorry

end FRouting
