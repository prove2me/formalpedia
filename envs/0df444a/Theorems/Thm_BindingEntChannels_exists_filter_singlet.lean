-- Prove2me | Theorems.Thm_BindingEntChannels_exists_filter_singlet
-- name    : BindingEntChannels.exists_filter_singlet
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:39:22.243695+00:00
-- url     : https://prove2.me/theorems/d8ddf4ba-201f-4a7a-9daf-33098db52a08
-- title:
--   §II, p. 2 — every state is $(\Gamma\otimes I)P_+$ for a CP map $\Gamma$
-- statement:
--   Let $I$ and $K$ be finite index sets. Every density matrix $\sigma$ on $\mathbb C^K\otimes\mathbb C^I$ can be written as
--
--   $$
--   \sigma=(\Gamma\otimes I)\,P^{I}_+
--   $$
--
--   for some completely positive map $\Gamma$ from operators on $\mathbb C^I$ to operators on $\mathbb C^K$, given by finitely many Kraus operators and not necessarily trace preserving.
--
--   The paper uses this with $\mathbb C^I=(\mathbb C^m)^{\otimes N}$ to rewrite the input of the most general protocol in terms of a singlet.
--
--   Differences from the source:
--   - generalization: σ on C^{k×N} ⊗ C^{m×N} (k^N- and m^N-dimensional factors) → σ on C^K ⊗ C^I for arbitrary finite index sets K, I; reason: the paper's case is I = Fin N → Fin m, K = Fin N → Fin k
--   - encoding: Γ is CP, but not necessarily trace-preserving → Γ given by a finite Kraus family G with no completeness condition; reason: every CP map between finite-dimensional matrix algebras has a finite Kraus form
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, §II, p. 2 (proof of the Theorem: "the state σ (as any state) can be written as …")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_ObliviousRSP_maxEnt
import Definitions.Def_BindingEntChannels_filterLeft

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
§II, p. 2 (proof of the Theorem): "the state σ (as any state) can be written as
σ = (Γ^{k×N}_{m×N} ⊗ I_{m×N})P^{m×N}_+ (where Γ is CP, but not necessarily trace-preserving
map)."

For finite index types `I`, `K` and every density matrix `σ` on `K × I` there is a CP map
`Γ : M_I → M_K`, given by a finite Kraus family `G`, with `σ = (Γ ⊗ I)P^I_+`.

**Formalization Note.** Stated for arbitrary finite types; the paper's case is
`I = Fin N → Fin m` (`m × N` denotes `m^N`) and `K = Fin N → Fin k`. No completeness condition
is imposed on `G`. At `I` empty there is no density matrix on `K × I`, so no `Nonempty` binder
is needed. `P^I_+` is the published `ObliviousRSP.maxEnt I`. -/
theorem exists_filter_singlet {I : Type} {K : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    [DecidableEq K] (σ : Matrix (K × I) (K × I) ℂ) (hσ : QAlgorithms.IsDensityMatrix σ) :
    ∃ (r : ℕ) (G : Fin r → Matrix K I ℂ), σ = filterLeft G (ObliviousRSP.maxEnt I) := by sorry

end BindingEntChannels
