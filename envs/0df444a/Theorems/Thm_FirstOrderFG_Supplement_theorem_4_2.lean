-- Prove2me | Theorems.Thm_FirstOrderFG_Supplement_theorem_4_2
-- name    : FirstOrderFG.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:02:28.773006+00:00
-- url     : https://prove2.me/theorems/8746d271-f190-46c0-942c-12f411e81523
-- title:
--   Theorem 4.2 — known-parameter first-order regret for Algorithm 2
-- statement:
--   Let $K\ge2$, $T\ge3$, and let $G$ be a strongly observable directed feedback graph with oblivious losses in $[0,1]^K$. If the self-loop meta-action exists, let $A\ge1$ bound $H^{G_{\mathrm{self}}}(q_t)$ on every round; otherwise take $A=1$. Write $M=|\mathcal B|$, $J=\lceil\log_2(2MT)\rceil$, $\Gamma_A=AJ\ln(KT)$, and $c=1/(2^{13}e^2)$.
--
--   There is a universal $C_1>0$ such that, whenever $0<\theta\le c/\Gamma_A$, published Algorithm 2 guarantees for every arm $k$ that
--
--   $$
--   \operatorname{Reg}^{\mathrm{Alg2}}_{T,k}
--   \le C_1\left(\frac{\ln(MT)}{\theta}+\Gamma_A\theta L_{T,k}\right).
--   $$
--
--   At $\theta=\min\{c/\Gamma_A,\sqrt{\ln(MT)/(\Gamma_A L^\star)}\}$, a universal $C_2>0$ gives
--
--   $$
--   \operatorname{Reg}^{\mathrm{Alg2}}_T
--   \le C_2\bigl(\sqrt{\Gamma_A\ln(MT)L^\star}+\Gamma_A\ln(MT)\bigr).
--   $$
--
--   Taking the Lemma 2.1 graph bound yields, for a universal $C_3>0$,
--
--   $$
--   \operatorname{Reg}^{\mathrm{Alg2}}_T
--   \le C_3\bigl(\ln^2(KT)\sqrt{\alpha L^\star}+\ln^4(KT)\alpha\bigr).
--   $$
--
--   Differences from the source:
--   - encoding: Algorithm 2 and its conditional expectation → the immutable published Algorithm 2 state machine started at round 1 and evaluated by its finite trajectory law; reason: reuses exactly the base mission's formalization of the printed algorithm
--   - encoding: "sufficiently small universal c" → c=1/(2¹³e²); reason: the proof of Theorem 4.2 fixes this value on p.31
--   - encoding: O and Õ conclusions → universal constants with the displayed rates and ln²(KT), ln⁴(KT) factors from the proof; reason: asymptotic notation must be made propositional and the proof supplies these powers
--   - encoding: √(ln(MT)/(Γ_A L⋆)) when L⋆=0 → the value +∞ before the minimum, hence c/Γ_A; reason: preserves the paper's positive-real convention instead of Lean real division's default zero
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Theorem 4.2, p.11; proof of Theorem 4.2, p.31

import Mathlib
import Definitions.Def_FirstOrderFG_StronglyObservable
import Definitions.Def_FirstOrderFG_InteriorStart
import Definitions.Def_FirstOrderFG_Vself
import Definitions.Def_FirstOrderFG_Bset
import Definitions.Def_FirstOrderFG_Hself
import Definitions.Def_FirstOrderFG_GammaA
import Definitions.Def_FirstOrderFG_cConst
import Definitions.Def_FirstOrderFG_Alg2_init
import Definitions.Def_FirstOrderFG_Alg2_qOf
import Definitions.Def_FirstOrderFG_Alg2_runFrom
import Definitions.Def_FirstOrderFG_Supplement_Alg2_RegK
import Definitions.Def_FirstOrderFG_Supplement_Alg2_Reg
import Definitions.Def_FirstOrderFG_Supplement_Alg2_boundA
import Definitions.Def_FirstOrderFG_Supplement_Alg2_tunedTheta
import Definitions.Def_FirstOrderFG_Lk
import Definitions.Def_FirstOrderFG_Lstar
import Definitions.Def_FirstOrderFG_indepNumber

set_option autoImplicit false

namespace FirstOrderFG.Supplement

/-- **Theorem 4.2 (known-parameter guarantee for Algorithm 2).**
Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*,
arXiv:2610.40861, Theorem 4.2, p.11, with its constant fixed in the proof on p.31.

If the self-loop meta-action exists, `A ≥ 1` bounds `H^{G_self}(q_t)` on every round;
otherwise `A=1`. With `0 < θ ≤ c/Γ_A`, where `c=1/(2¹³e²)`, published
Algorithm 2 has the per-arm bound
`O(ln(MT)/θ + Γ_A θ L_{T,k})`. Its tuned rate is
`O(√(Γ_A ln(MT)L⋆) + Γ_A ln(MT))`; the Lemma 2.1 choice gives the full
`O(ln²(KT)√(αL⋆) + ln⁴(KT)α)` reading of `Õ(√(αL⋆)+α)`.

**Formalization Note.** Algorithm 2 is reused unchanged from the published base mission.
`Alg2.expLoss` merely starts that state machine at round one and applies its published finite-tree
expectation. The constants hidden by the three asymptotic clauses are universal and precede all
instance data. The Picard start is any published `InteriorStart`, matching Proposition A.3.
`Alg2.tunedTheta` handles `L⋆=0` using the extended positive-real convention of the printed
minimum rather than Lean's zero-valued real division. -/
theorem theorem_4_2 :
    ∃ Cmain Copt Ctilde : ℝ, 0 < Cmain ∧ 0 < Copt ∧ 0 < Ctilde ∧
      ∀ (K T : ℕ), 2 ≤ K → 3 ≤ T →
      ∀ (E : Fin K → Fin K → Prop) [DecidableRel E],
        FirstOrderFG.StronglyObservable E →
      ∀ ℓ : ℕ → Fin K → ℝ,
        (∀ t ∈ Finset.Icc 1 T, ∀ i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ, FirstOrderFG.InteriorStart E q₀ →
        (∀ (A θ : ℝ), 1 ≤ A →
          (((FirstOrderFG.Vself E).Nonempty ∧
              ∀ h : List (Fin K), h.length < T →
                FirstOrderFG.Hself E T
                  (FirstOrderFG.Alg2.qOf E T q₀
                    (FirstOrderFG.Alg2.runFrom E T ℓ q₀ 1
                      (FirstOrderFG.Alg2.init E A θ) h)) ≤ A) ∨
            (¬(FirstOrderFG.Vself E).Nonempty ∧ A = 1)) →
          0 < θ → θ ≤ FirstOrderFG.cConst / FirstOrderFG.GammaA E T A →
          ∀ k : Fin K,
            Alg2.RegK E T ℓ q₀ A θ k ≤
              Cmain *
                (Real.log (((FirstOrderFG.Bset E).card : ℝ) * T) / θ +
                  FirstOrderFG.GammaA E T A * θ * FirstOrderFG.Lk T ℓ k)) ∧
        (∀ A : ℝ, 1 ≤ A →
          (((FirstOrderFG.Vself E).Nonempty ∧
              ∀ h : List (Fin K), h.length < T →
                FirstOrderFG.Hself E T
                  (FirstOrderFG.Alg2.qOf E T q₀
                    (FirstOrderFG.Alg2.runFrom E T ℓ q₀ 1
                      (FirstOrderFG.Alg2.init E A
                        (Alg2.tunedTheta E T A (FirstOrderFG.Lstar T ℓ))) h)) ≤ A) ∨
            (¬(FirstOrderFG.Vself E).Nonempty ∧ A = 1)) →
          Alg2.Reg E T ℓ q₀ A (Alg2.tunedTheta E T A (FirstOrderFG.Lstar T ℓ)) ≤
            Copt *
              (Real.sqrt
                  (FirstOrderFG.GammaA E T A *
                    Real.log (((FirstOrderFG.Bset E).card : ℝ) * T) *
                    FirstOrderFG.Lstar T ℓ) +
                FirstOrderFG.GammaA E T A *
                  Real.log (((FirstOrderFG.Bset E).card : ℝ) * T))) ∧
        Alg2.Reg E T ℓ q₀ (Alg2.boundA E T)
            (Alg2.tunedTheta E T (Alg2.boundA E T) (FirstOrderFG.Lstar T ℓ)) ≤
          Ctilde *
            (Real.log ((K : ℝ) * T) ^ 2 *
                Real.sqrt (FirstOrderFG.indepNumber E * FirstOrderFG.Lstar T ℓ) +
              Real.log ((K : ℝ) * T) ^ 4 * FirstOrderFG.indepNumber E) := by sorry

end FirstOrderFG.Supplement
