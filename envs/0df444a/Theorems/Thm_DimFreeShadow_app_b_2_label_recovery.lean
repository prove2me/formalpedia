-- Prove2me | Theorems.Thm_DimFreeShadow_app_b_2_label_recovery
-- name    : DimFreeShadow.app_b_2_label_recovery
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:03:39.619528+00:00
-- url     : https://prove2.me/theorems/12ef01a5-1753-46bd-8477-19c08061dc33
-- title:
--   App. B.2 — completion of the label recovery and the spectator identity
-- statement:
--   Let $\omega_{JKC}$ be a state with $J$ classical, $\omega_{JK}=\sum_a|a\rangle\langle a|\otimes C_a$, $B=\sum_aC_a=\omega_K$, $P=\Pi_{\operatorname{supp}B}$, $Q=\Pi_{\operatorname{supp}\omega_C}$. Let $\tau=\omega_{JK}\otimes\omega_C$ and $\mathcal N=\operatorname{Tr}_J$. Then:
--
--   1. $\operatorname{supp}\omega_{JKC}\subseteq\operatorname{supp}\tau$ and $\operatorname{supp}\omega_{KC}\subseteq\operatorname{supp}B\otimes\operatorname{supp}\omega_C$;
--   2. each rotated label recovery $R_u$ is completely positive with $\operatorname{Tr}R_u(X)=\operatorname{Tr}(PX)$, and $R=\int\beta_0R_u$ preserves the trace of operators supported on $\operatorname{supp}B$;
--   3. the completion $\widehat R(X)=R(PXP)+\operatorname{Tr}((I-P)X)\omega_{JK}$ is a channel;
--   4. on every operator supported on $P\otimes Q$, correlated operators included, the rotated map of Eq. (19) for $\tau,\mathcal N$ equals $R_u\otimes\mathrm{id}_C$, also when $\omega_C$ is singular;
--   5. the recovered state of Theorem 4.2 on the input $\omega_{KC}$ is $(\widehat R\otimes\mathrm{id}_C)(\omega_{KC})$.
--
--   The source also states: "Therefore $R=\int_{\mathbb R}\beta_0(u)R_u\,du$ preserves trace on this support. Its full-space completion is $\widehat R(X)=R(PXP)+\operatorname{Tr}((I-P)X)\omega_{JK}$. (41) Both terms are completely positive, and their traces sum to $\operatorname{Tr}(PX)+\operatorname{Tr}((I-P)X)=\operatorname{Tr}X$. Thus this completion is a channel."
--
--   This identity is what lets Theorem 4.2, applied with a classical label and a spectator copy, be read as a measurement on the prefix alone.
--
--   Differences from the source:
--   - encoding: completely positive → an explicit Kraus form R_u(X) = Σ_a V_a X V_a† with no normalization condition; reason: each block is a congruence, which is how the source justifies complete positivity
--   - encoding: R_u ⊗ id_C on J ⊗ K ⊗ C → tensorIdRight reindexed from (A × κ) × γ to A × (κ × γ) by the associator; reason: Lean index types; the same operator
--   - encoding: J classical → ω block diagonal in the label index A; reason: this is what a classical register means in matrix form
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), App. B.2, p.36

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_WildeQIT_Recover_spectralFun
import Definitions.Def_DimFreeShadow_labelRecovery

namespace DimFreeShadow

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported rotatedPetz recovery)

/-- **The recovery map on a classical register** (arXiv:2608.06345, sha256 a1a42249…,
App. B.2, p.36). Let `ω_{JKC}` be a state with `J` classical, `ω_{JK} = Σ_a |a⟩⟨a| ⊗ C_a`,
`B = Σ_a C_a = ω_K`, `P = Π_{supp B}`, `Q = Π_{supp ω_C}`, `α = (1 − iu)/2`. Then:
1. each rotated map `R_u(X) = Σ_a |a⟩⟨a| ⊗ C_a^α B^{−α} X B^{−ᾱ} C_a^{ᾱ}` is completely positive
   (a sum of congruences) with `Tr R_u(X) = Tr(PX)`, and `R = ∫ β₀ R_u` preserves the trace of
   operators supported on `supp B`;
2. the completion `R̂(X) = R(PXP) + Tr((I − P)X) ω_{JK}` (41) is a channel;
3. for the reference `τ = ω_{JK} ⊗ ω_C` and the channel `N = Tr_J`, the rotated map of Eq. (19)
   equals `R_u ⊗ id_C` on every operator supported on `P ⊗ Q`, correlated operators included
   (the spectator identity, also for singular `ω_C`);
4. the recovered state `(R_{τ,N} ∘ N)(ω_{JKC})` of Theorem 4.2 is `(R̂ ⊗ id_C)(ω_{KC})`;
5. `supp ω_{JKC} ⊆ supp τ` and `supp ω_{KC} ⊆ supp B ⊗ supp ω_C`.

**Formalization Note** `J, K, C` are indexed by `A, κ, γ`, and `ω_{JKC}` by
`A × (κ × γ)`; "`J` classical" is block diagonality in `J`. `C_a`, `ω_C`, `ω_{KC}` and
`τ = ω_{JK} ⊗ ω_C` are the partial traces/products written out. The rotated map of Eq. (19) is
the published `P21.rotatedPetz τ Tr_J (u/2)` and `R_{τ,N}` is `P21.recovery τ Tr_J`, with
`Tr_J = QAlgorithms.traceLeft`. `R_u ⊗ id_C` (output on `(A × κ) × γ`) is reindexed to
`A × (κ × γ)` by the associator. Complete positivity of `R_u` is stated as a Kraus form
`R_u(X) = Σ_a V_a X V_a†` (no normalization); a channel is `QAlgorithms.IsChannel`. -/
theorem app_b_2_label_recovery {A κ γ : Type} [Fintype A] [DecidableEq A] [Fintype κ]
    [DecidableEq κ] [Fintype γ] [DecidableEq γ]
    (ω : Matrix (A × (κ × γ)) (A × (κ × γ)) ℂ) (hω : WildeQIT.IsDensityOperator ω)
    (hcl : ∀ a a' : A, a ≠ a' → ∀ x x' : κ × γ, ω (a, x) (a', x') = 0) :
    let C : A → Matrix κ κ ℂ := fun a => Matrix.of fun k k' => ∑ c, ω (a, (k, c)) (a, (k', c))
    let ωC : Matrix γ γ ℂ := Matrix.of fun c c' => ∑ a, ∑ k, ω (a, (k, c)) (a, (k, c'))
    let τ : Matrix (A × (κ × γ)) (A × (κ × γ)) ℂ :=
      Matrix.of fun p q => blockDiag C (p.1, p.2.1) (q.1, q.2.1) * ωC p.2.2 q.2.2
    let P : Matrix κ κ ℂ := WildeQIT.Recover.supportProj (∑ a, C a)
    let PQ : Matrix (κ × γ) (κ × γ) ℂ := Matrix.kroneckerMap (· * ·) P (WildeQIT.Recover.supportProj ωC)
    IsSupported ω τ ∧ PQ * QAlgorithms.traceLeft ω = QAlgorithms.traceLeft ω ∧
    (∀ u : ℝ, (∃ Vk : A → Matrix (A × κ) κ ℂ,
        ∀ X : Matrix κ κ ℂ, labelRotated C u X = ∑ a, Vk a * X * (Vk a).conjTranspose) ∧
      ∀ X : Matrix κ κ ℂ, (labelRotated C u X).trace = (P * X).trace) ∧
    (∀ X : Matrix κ κ ℂ, P * X * P = X → (labelRecovery C X).trace = X.trace) ∧
    QAlgorithms.IsChannel (labelCompletion C) ∧
    (∀ u : ℝ, ∀ X : Matrix (κ × γ) (κ × γ) ℂ, PQ * X * PQ = X →
      rotatedPetz τ (QAlgorithms.traceLeft (α := A) (β := κ × γ)) (u / 2) X =
        Matrix.reindex (Equiv.prodAssoc A κ γ) (Equiv.prodAssoc A κ γ)
          (tensorIdRight (γ := γ) (labelRotated C u) X)) ∧
    recovery τ (QAlgorithms.traceLeft (α := A) (β := κ × γ)) (QAlgorithms.traceLeft ω) =
      Matrix.reindex (Equiv.prodAssoc A κ γ) (Equiv.prodAssoc A κ γ)
        (tensorIdRight (γ := γ) (labelCompletion C) (QAlgorithms.traceLeft ω)) := by sorry

end DimFreeShadow
