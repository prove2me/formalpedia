-- Prove2me | Theorems.Thm_BddExp3SUM_certificate_parameters
-- name    : BddExp3SUM.certificate_parameters
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:54.613991+00:00
-- url     : https://prove2.me/theorems/ea07fdb5-d9d9-43e5-b8dd-fb5d0865209a
-- title:
--   §3: the least row count $\ell\ge1$, the certificate (3), and $q\ge1$, $R/M<D\le R$, $\ell\ge\frac14\log_Mn$, $q\le\eta\log_2n\le\frac18\log_Mn$
-- statement:
--   Let $M\ge2$, $n\ge16$, $R\ge M$, and let $(s_d)_{d\in\mathcal D}$ be values with $s_M\ge n^{1/4}$. Then
--
--   $$n^\eta/2\le R\le n^\eta,\qquad R^\alpha/2\le\sigma\le R^\alpha\le\sqrt R,$$
--
--   a least $\ell$ with $d^\ell\sigma\ge s_dR$ for all $d\in\mathcal D$ exists, and for it $\ell\ge1$, some $e\in\mathcal D$ satisfies
--
--   $$e^\ell<es_eR/\sigma,$$
--
--   and $\ell\ge\frac14\log_Mn$. For every $e\in\mathcal D$ and prime $p\mid e$, with $q=\lfloor\log_pR\rfloor$ and $D=p^q$,
--
--   $$q\ge1,\quad R/M<D\le R,\quad q\le\eta\log_2n\le\tfrac18\log_Mn,\quad q\le\ell.$$
--
--   This is the extremal divisor certificate: all divisors obey the lower bound, and one divisor obeys the complementary upper bound.
--
--   Differences from the source:
--   - generalization: s_d the profile values of a subinstance; e the certificate divisor → any values s with s_M ≥ n^{1/4}, and the bounds on q, D for every e ∈ 𝒟; reason: the argument uses only s_M ≥ n^{1/4} (Lemma 2 supplies it); the source’s choice is a special case
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group, STOC 2027 submission (manuscript sha256 19546c9a…), §3, (1)–(3), p.3 (PDF p.4)

import Mathlib
import Definitions.Def_BddExp3SUM_Profiles

namespace BddExp3SUM

/-- §3, p.3 (Zeng, Wang, Cao, Dai, Wang, STOC 2027 submission, manuscript sha256 19546c9a…): the bounds
on `R, σ` below (1), the existence of the least `ℓ` of (2), `ℓ ≥ 1`, the certificate (3), and
`q ≥ 1`, `R/M < D ≤ R`, `ℓ ≥ (1/4) log_M n`, `q ≤ η log₂ n ≤ (1/8) log_M n`, `k = ℓ - q ≥ 0`.

**Formalization Note.** The values `s_d` are any function `s` with `s_M ≥ n^{1/4}`, the only property of
the profile values that this argument uses. -/
theorem certificate_parameters {M n : ℕ} (hM : 2 ≤ M) (hn : 16 ≤ n) (hR : M ≤ R M n) (s : ℕ → ℕ)
    (hs : (n : ℝ) ^ ((1 : ℝ) / 4) ≤ s M) :
    ((n : ℝ) ^ η M / 2 ≤ R M n ∧ (R M n : ℝ) ≤ (n : ℝ) ^ η M) ∧
    ((R M n : ℝ) ^ α / 2 ≤ σ M n ∧ (σ M n : ℝ) ≤ (R M n : ℝ) ^ α ∧
      (R M n : ℝ) ^ α ≤ √(R M n : ℝ)) ∧
    (∃ ℓ : ℕ, IsLeast {ℓ : ℕ | ∀ d ∈ Dvs M, s d * R M n ≤ d ^ ℓ * σ M n} ℓ) ∧
    ∀ ℓ : ℕ, IsLeast {ℓ : ℕ | ∀ d ∈ Dvs M, s d * R M n ≤ d ^ ℓ * σ M n} ℓ →
      1 ≤ ℓ ∧
      (∃ e ∈ Dvs M, (e : ℝ) ^ ℓ < e * s e * R M n / σ M n) ∧
      (1 / 4 : ℝ) * Real.logb M n ≤ ℓ ∧
      ∀ e ∈ Dvs M, ∀ p : ℕ, p.Prime → p ∣ e →
        let q := Nat.log p (R M n)
        1 ≤ q ∧ (R M n : ℝ) / M < (p ^ q : ℕ) ∧ p ^ q ≤ R M n ∧
        (q : ℝ) ≤ η M * Real.logb 2 n ∧
        η M * Real.logb 2 n ≤ (1 / 8 : ℝ) * Real.logb M n ∧
        q ≤ ℓ := by sorry

end BddExp3SUM
