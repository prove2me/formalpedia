-- Prove2me | Theorems.Thm_CritWinSpin_lemma_7_1
-- name    : CritWinSpin.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:46:30.941096+00:00
-- url     : https://prove2.me/theorems/a1be84f7-ada5-4688-b7a1-cf08a2882c7e
-- title:
--   Lemma 7.1, p.26 — a rejected or unreached message is unpredictable, (39)
-- statement:
--   Let $F_{1:T}\sim V^{\otimes T}$ with $V=\mathrm{Unif}(\Omega)$, let $\Psi(F)$ be uniform on $\{0,1\}^d$ under $V$, and let $X_{1:k}=\hat L_{T,k}(F_{1:T})$. Let $X'_{1:k+1}$ be drawn from $X_{1:k}$. For every $i\in[T]$,
--   $$\mathbb P\{\mathrm{Pass},\ X_{1:k}\ne\bot,\ i\notin I_{\mathrm{acc}},\ m^*=\Psi(F_i)\}\le2^{-d}.$$
--
--   This excludes the second alternative of (38) in the proof of the lower bound.
--
--   Differences from the source:
--   - generalization: L̂_{T,k} of Theorem 6.3, a learner A, the source of Theorem 5.1 at a key P → any slot kernel, any stochastic kernel from X_{1:k} to X′_{1:k+1}, any Ω and Ψ with Ψ uniform under Unif(Ω); reason: the proof uses only that the slots are independent and that each reads its own F_t; extension and amplification are instances of the kernel; the paper's source has uniform Ψ by Theorem 5.1(ii)
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Lemma 7.1, p.26, eq. (39); §7, p.26

import Mathlib
import Definitions.Def_CritWinSpin_Lhat
set_option autoImplicit false

namespace CritWinSpin

open Classical in
/-- **Lemma 7.1** (Liu–Zhang–Ren, STOC 2027 submission, manuscript sha256 f77584da…, p.26). Let
`F_{1:T} ∼ V^{⊗T}` with `V` uniform on `Ω` and `Ψ(F)` uniform on `{0,1}^d` under `V`, and
`X_{1:k} = L̂_{T,k}(F_{1:T})`. For any slot kernel `κ`, any kernel `Al` from `X_{1:k}` to `X'_{1:k+1}` and
every `i ∈ [T]`: `P{Pass, X_{1:k} ≠ ⊥, i ∉ I_acc, m* = Ψ(F_i)} ≤ 2^{−d}`, eq. (39).

**Formalization Note.** Extension (`X' = (X_{1:k}, A(M, X_{1:k}))`) and amplification
(`X' = A(M, X_{1:k})`) are both instances of `Al`. The proof uses only that the slots are independent and
that each depends on its own `F_t`, so no efficiency or Theorem 6.3 hypothesis is needed. -/
theorem lemma_7_1 (S : SpinLaw) {n r d k T : ℕ} (Ω : Finset (BinCfg n)) (Ψ : BinCfg n → Fin d → Bool)
    (hΨ : ∀ m₀ : Fin d → Bool, ∑ y, unifOn Ω y * (if Ψ y = m₀ then (1 : ℝ) else 0) = 1 / (2 : ℝ) ^ d)
    (κ : BinCfg n → Option (Config S (Fin n × Fin r)) → ℝ)
    (hκ₀ : ∀ y o, 0 ≤ κ y o) (hκ₁ : ∀ y, ∑ o, κ y o = 1)
    (Al : (Fin k → Config S (Fin n × Fin r)) → Option (Fin (k + 1) → Config S (Fin n × Fin r)) → ℝ)
    (hAl₀ : ∀ X o, 0 ≤ Al X o) (hAl₁ : ∀ X, ∑ o, Al X o = 1) (i : Fin T) :
    ∑ Fs : Fin T → BinCfg n, prodLaw (unifOn Ω) Fs *
      ∑ ω : Fin T → Option (Config S (Fin n × Fin r)), (∏ t, κ (Fs t) (ω t)) *
        (match lhatRun k ω with
         | none => 0
         | some R =>
            ∑ X' : Fin (k + 1) → Config S (Fin n × Fin r), Al (fun j => (R j).2) (some X') *
              (if PassEv Ω Ψ X' ∧ (∀ j, (R j).1 ≠ i) ∧
                  mStar Ψ (fun j => (R j).2) X' = some (Ψ (Fs i)) then (1 : ℝ) else 0)) ≤
      1 / (2 : ℝ) ^ d := by sorry

end CritWinSpin
