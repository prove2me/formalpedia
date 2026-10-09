-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_smoothed_bombieri_vinogradov
-- name    : ArtinPrimitiveRoots.smoothed_bombieri_vinogradov
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T14:11:24.941247+00:00
-- url     : https://prove2.me/theorems/e8de0b93-d806-47c0-9481-151ede6bdef7
-- title:
--   Proof of Lemma 12.3 (OpenAI), (12.16) → (12.18) — Bombieri–Vinogradov for smoothed prime sums
-- statement:
--   Let $A' > 0$ and $0 < \eta < 1/2$. Then there is $C \ge 0$ with the following property. Let $2 \le T_1 \le T_2$, and let $f : \mathbb R \to \mathbb R$ be differentiable with continuous derivative, with $f(t) = f'(t) = 0$ whenever $t \le T_1$ or $t \ge T_2$, and with $|f'| \le B$ everywhere. Let $S$ be a finite set of moduli $q$ with $1 \le q < T_1^{1/2-\eta}$, and for each $q \in S$ let $v_q$ be a residue class with $(v_q, q) = 1$. Then
--
--   $$\sum_{q \in S}\Bigl|\sum_{\substack{p \le T_2 \text{ prime}\\ p \equiv v_q\ (q)}} f(p) - \frac{1}{\varphi(q)}\int_{T_1}^{T_2}\frac{f(t)}{\log t}\,dt\Bigr| \;\le\; C\,B\,(T_2 - T_1)\,T_2\,(\log T_1)^{-A'}.$$
--
--   The inner sum runs over $k \in \{0, \dots, \lfloor T_2\rfloor\}$ with $k$ prime and $k \equiv v_q \pmod q$ (`Nat.ModEq`), and the integral is an interval integral.
--
--   **Formalization note.** The paper applies partial summation to (12.16) for the particular weight $t \mapsto \Psi((crt + 1)/x)$ and the moduli $N\ell$, and checks the uniformity in words. The statement here is that step for a general weight: the bound is the total variation $B(T_2 - T_1)$ of the weight times the Bombieri–Vinogradov bound at the largest point $T_2$. The modulus range $q < T_1^{1/2-\eta}$ is the range of (12.16) at every point $t \ge T_1$ of the integration.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 78: “Partial summation in (12.16) yields $\sum_{\ell \le D,\ \ell \text{ odd squarefree}}\Bigl|A_r(\ell) - \frac{g_r(\ell)}{\varphi(N)}I_r\Bigr| \ll_{A'} \frac xr L^{-A'}$. (12.18) To check the smoothing uniformly, integrate the progression remainder against the derivative of $\Psi((crt + 1)/x)$. Its total absolute integral is $\int|\Psi'(y)|\,dy$, independently of $r$, and all integration points have $t \asymp x/(cr)$. The moduli $N\ell$ are distinct, and the maximum in (12.16) covers their varying residue classes.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 77–78, proof of Lemma 12.3, (12.16) → (12.18)

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

theorem smoothed_bombieri_vinogradov (A' η : ℝ) (hA' : 0 < A') (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ → ℝ) (T₁ T₂ B : ℝ), Differentiable ℝ f → Continuous (deriv f) →
      (∀ t, t ≤ T₁ ∨ T₂ ≤ t → f t = 0 ∧ deriv f t = 0) → 2 ≤ T₁ → T₁ ≤ T₂ →
      (∀ t, |deriv f t| ≤ B) → ∀ (S : Finset ℕ) (v : ℕ → ℕ),
      (∀ q ∈ S, 1 ≤ q ∧ (q : ℝ) < T₁ ^ (1 / 2 - η) ∧ Nat.Coprime (v q) q) →
      ∑ q ∈ S, |∑ k ∈ (Finset.Icc 0 ⌊T₂⌋₊).filter (fun k => k.Prime ∧ k ≡ v q [MOD q]), f k -
          (1 / (Nat.totient q : ℝ)) * ∫ t in T₁..T₂, f t * (1 / log t)| ≤
        C * (B * ((T₂ - T₁) * (T₂ * log T₁ ^ (-A')))) := by
  sorry

end ArtinPrimitiveRoots
