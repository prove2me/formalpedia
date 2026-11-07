-- Prove2me | Theorems.Thm_AdaptiveSparsify_lemma_4_7
-- name    : AdaptiveSparsify.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:47:19.084708+00:00
-- url     : https://prove2.me/theorems/470dea93-ccf6-433f-a37d-444ae868b299
-- title:
--   Lemma 4.7 — the centrality potential decreases in conditional expectation
-- statement:
--   Let $(x,s)$ be $\varepsilon$ well-centered at $t$ with feasibility error at most $\alpha^2$, take a step of Algorithm 1 with $R$ drawn as in Lemma 6.3, and put $\hat t=(1-\eta)t$ for $\eta=\varepsilon\alpha/(C_{\mathrm{center}}\sqrt\nu)$, where $\nu=\sum_i\nu_i$. Let $G$ be the event that items 5 and 6 of Definition 4.6 and the conclusion of Lemma 4.13 hold for the sample. Then $\Pr[G]>0$ and
--
--   $$\mathbb E\big[\Psi^{\hat t}(x^{\mathrm{new}},s^{\mathrm{new}})\mid G\big]\le\Big(1-\frac{\varepsilon\alpha}{C_{\mathrm{center}}^2\sqrt\nu}\Big)\Psi^t(x,s)+O(n^2).$$
--
--   Iterating this bound through the stopped process of §6.3 keeps every iterate well-centered with high probability.
--
--   Differences from the source:
--   - reading: "The expectation below is over the samples for which …" → the conditional expectation on that event, with the event having positive probability; reason: the stronger reading; p.44 calls it the conditional expectation
--   - reading: "sufficiently small" ε, large C_center, C_var and sample constant, C_K absolute → explicit quantifiers: C_K, then ε₀, then ε, then the other constants in the order of the proof, all before the instance; reason: p.17 and §6.4 hide these constants; they may depend on C_K, which is an absolute constant (reading R1)
--   - reading: §4 assumes n large enough for log n > 0 → n ≥ 2; reason: λ = C_center log n / ε² vanishes at n = 1 and α is then undefined
--   - reading: the conclusion mentions ∇²Φ(x^new) only → x^new is also required to lie in the barrier domain; reason: the norm at x^new means nothing outside the domain, and the proof obtains membership from Lemma 4.12
--   - reading: ν = Σν_i for "constants ν_i" → any barrier parameters ν_i ≤ C_K of the φ_i; reason: §4.1, with the bound of reading R6
--   - reading: O(n²) → D n² for a constant D chosen after the other constants and before the instance; reason: the meaning of O (reading R1)
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Lemma 4.7, p.19

import Mathlib
import Definitions.Def_AdaptiveSparsify_IPM

open Matrix

namespace AdaptiveSparsify

/-- **Lemma 4.7** (Potential Maintenance), p.19.

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…), Lemma 4.7, p.19.

"Assume that (x, s) are ε well-centered at path parameter t with feasibility error
‖A⊤x − b‖_{(A⊤∇²Φ(x)⁻¹A)⁻¹} ≤ α² (which Lemma 4.13 guarantees after every step, and which the exactly
feasible initial point satisfies), and that R is drawn by Lemma 6.3. The expectation below is over the
samples for which items 5 and 6 of Definition 4.6 and the conclusion of Lemma 4.13 hold; the remaining
samples have probability n^{−Ω(1)} and are handled by the stopped process in Section 6.3. Let
t̂ = (1 − η)t for η = εα/(C_center √ν). It holds that
E[Ψ^{t̂}(x^new, s^new)] ≤ (1 − εα/(C²_center √ν)) Ψ^t(x, s) + O(n²)."

**Formalization Note.** The expectation over the good samples is read as the conditional expectation on
that event (the stronger reading), and the good event has positive probability. The conclusion of Lemma
4.13 includes `x^new` in the barrier domain, so `Ψ` is never evaluated at a junk point. `ν = ∑ ν_i` for any
barrier parameters `ν_i ≤ C_K` of the `φ_i`. The constants are chosen in the order `ε`, `C_center`, `C_var`,
the sampling constant, and the `O(n²)` constant. -/
theorem lemma_4_7 : ∀ CK : ℕ, 1 ≤ CK → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 80 ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ Cc₀ : ℝ, 0 < Cc₀ ∧ ∀ Cc : ℝ, Cc₀ ≤ Cc →
      ∃ Cv₀ : ℝ, 0 < Cv₀ ∧ ∀ Cvar : ℝ, Cv₀ ≤ Cvar →
        ∃ Cs₀ : ℝ, 0 < Cs₀ ∧ ∀ Cs : ℝ, Cs₀ ≤ Cs → ∃ D : ℝ, 0 < D ∧
          ∀ I : ERMInstance, I.IsAdmissible CK → 2 ≤ I.blocks.n →
          ∀ ν : Fin I.blocks.m → ℝ,
            (∀ i, EntropicBarrier.Universal.IsNuSelfConcordantBarrier (I.K i) (I.φ i) (ν i)) →
            (∀ i, ν i ≤ CK) →
          ∀ (t : ℝ) (x s : Fin I.blocks.n → ℝ) (ch : I.StepChoice), 0 < t →
            let p : Params := ⟨CK, ε, Cc⟩
            let n := I.blocks.n
            let α := p.alpha n
            let νsum := ∑ i, ν i
            let η := ε * α / (Cc * Real.sqrt νsum)
            I.WellCentered α ε t x s → I.feasErr x ≤ α ^ 2 → ch.Valid p t x s →
            let w := sampleWeight (K' := ch.stepCount p Cs) (ch.stepP p t x)
            let G := ch.GoodSample p Cs Cvar t x
            0 < probOf w G ∧
            condExpOf w G (fun idx =>
                I.Psi (p.lam n) ((1 - η) * t) (ch.xAt p Cs t x idx) (ch.sNew p t s)) ≤
              (1 - ε * α / (Cc ^ 2 * Real.sqrt νsum)) * I.Psi (p.lam n) t x s +
                D * (n : ℝ) ^ 2 := by sorry

end AdaptiveSparsify
