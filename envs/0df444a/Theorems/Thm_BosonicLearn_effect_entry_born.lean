-- Prove2me | Theorems.Thm_BosonicLearn_effect_entry_born
-- name    : BosonicLearn.effect_entry_born
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T06:16:19.190611+00:00
-- url     : https://prove2.me/theorems/644a3e89-1fa0-4296-b4ac-c403a155ac1d
-- title:
--   Entries of POVM effects are fixed combinations of four Born probabilities: $E(B)_{ab}=\sum_k c_k P_{\tau_k}(B)$
-- statement:
--   Every matrix entry of a POVM effect is a fixed complex combination of the outcome probabilities of four fixed states.
--
--   Let $I$ be an index set and $a,b\in I$. There are four density operators $\tau_0,\dots,\tau_3$ on $\ell^2(I)$ and four complex numbers $c_0,\dots,c_3$, depending only on $a$ and $b$, such that $\sum_kc_k=\delta_{ab}$ and, for every POVM $P$ on $\ell^2(I)$ with outcomes in any measurable space $O$, effects $E(B)$ and outcome laws $P_\rho$, and for every measurable $B\subseteq O$,
--
--   $$
--   E(B)_{ab}=\sum_{k=0}^{3}c_k\,P_{\tau_k}(B).
--   $$
--
--   For $a\neq b$ one can take the pure states $\tau_k=|\psi_k\rangle\langle\psi_k|$ with $\psi_k=(|a\rangle+\omega_k|b\rangle)/\sqrt2$, $(\omega_k)=(1,-1,\mathrm i,-\mathrm i)$, and $(c_k)=(\tfrac12,-\tfrac12,-\tfrac{\mathrm i}2,\tfrac{\mathrm i}2)$; for $a=b$, $\tau_k=|a\rangle\langle a|$ and $c=(1,0,0,0)$.
--
--   Role. Since the states and coefficients do not depend on the POVM, the identity holds simultaneously for a whole family $(Q_x)_{x\in\Omega}$ of POVMs. If the outcome laws $x\mapsto (Q_x)_\tau$ are Markov kernels, every entry $x\mapsto Q_x(B)_{ab}$ is therefore measurable, and $x\mapsto Q_x(C_x)_{ab}$ is measurable for measurable $C\subseteq\Omega\times O$. Conversely the effects of a POVM are recovered from its outcome laws. Both uses occur in the proof of `BosonicLearn.fockPOVM_compose`.
--
--   **Formalization Note** $P$ is a `FockPOVM I O` and the probability is `(P.law (τ k) B).toReal`. The quantifier over the outcome type `O : Type` is inside the existential, so the same `τ` and `coef` serve all POVMs. This strengthens the second part of `BosonicLearn.fockPOVM_form_measure`, where the four measures depend on the POVM.
--
--   **Related platform material** The space $\ell^2(A)$ used here (`Hilbert A`) is the same Lean type as `OAI.TensorLp.H A`, and $\ell^2(\mathbb N^n)$ is the same type as `OAI.EntropyPhotonNumber.Fock n`. The published definitions `OAI_Analysis_TensorLp` (tensor products, slices and operator lifts on $\ell^2(A\times B)$) and `OAI_MathematicalPhysics_Fock_Operators` (`OAI.CrossEnsemble.operator`, the bounded operator $\sum_i|u_i\rangle\langle v_i|$ of a family, with `hasSum_operator` and `entry_hasSum`) are sorry-free and can be imported. Proved lemmas of this mission that can be imported: `BosonicLearn.traceDist_le_one` (nuclear expansions, truncation to finite index sets) and `BosonicLearn.effect_matrix_operator` (effect matrices as bounded positive operators).
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, pp. 4–5 (Fock basis; general POVM measurements); auxiliary lemma for the proof of Theorem 3, p. 67

import Mathlib
import Definitions.Def_BosonicLearn_FockPOVM

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open MeasureTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Matrix entries of POVM effects are fixed combinations of four Born probabilities.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, p. 5 (general POVM measurements; outcome probabilities `Tr(E ρ)` in the Fock basis
`{|m⟩}` of p. 4).

For basis indices `a, b ∈ I` there are four density operators `τ₀, …, τ₃` on `ℓ²(I)` and four complex numbers
`c₀, …, c₃`, depending only on `a` and `b`, such that for **every** POVM `P` on `ℓ²(I)` (any outcome space) and
every measurable set `B` of outcomes

`E(B)_ab = ∑ₖ cₖ · Pr_P[outcome ∈ B | state τₖ]`,

and `∑ₖ cₖ = δ_ab`.

**Formalization Note.** The probabilities are `(P.law (τ k) B).toReal`. For `a ≠ b` the states are the pure
states `(|a⟩ + ω|b⟩)/√2`, `ω ∈ {1, −1, i, −i}` (polarization); for `a = b` they are `|a⟩⟨a|`. -/
theorem effect_entry_born {I : Type} [DecidableEq I] (a b : I) :
    ∃ (τ : Fin 4 → Matrix I I ℂ) (coef : Fin 4 → ℂ), (∀ c, IsDensity (τ c)) ∧
      (∑ c, coef c = (1 : Matrix I I ℂ) a b) ∧
      ∀ (O : Type) [MeasurableSpace O] (P : FockPOVM I O) (B : Set O), MeasurableSet B →
        P.effect B a b = ∑ c, coef c * (((P.law (τ c) B).toReal : ℝ) : ℂ) := by sorry

end BosonicLearn
