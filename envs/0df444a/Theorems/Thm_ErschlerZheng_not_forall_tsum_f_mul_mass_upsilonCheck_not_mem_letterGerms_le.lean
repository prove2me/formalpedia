-- Prove2me | Theorems.Thm_ErschlerZheng_not_forall_tsum_f_mul_mass_upsilonCheck_not_mem_letterGerms_le
-- name    : ErschlerZheng.not_forall_tsum_f_mul_mass_upsilonCheck_not_mem_letterGerms_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:16:52.230568+00:00
-- url     : https://prove2.me/theorems/27dd9aff-ec7c-4d59-9d7e-0931e9cb8e9e
-- title:
--   Proposition 7.12, as printed, fails for υ̌_n — the term x = o makes Σ_x f(d_𝒮(o, x)) υ̌_n{g : (g, x) ∉ ℋ^b} ⩽ C 2^n f(2^{n+2k_n}) false
-- statement:
--   It is not true that for every $D$, every string $\omega$ satisfying Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), every sequence $(k_n)$ satisfying the standing assumption of p. 40 (`IsAdmissibleSeq`) and every real $D' > D$, there is a constant $C$ such that for every $f : \mathbb R \to \mathbb R$ that is non-negative and non-increasing on $[0, \infty)$ with $f(2s)/f(s) \ge 2^{-1/D'}$ for all $s \ge 1$, and every $n$ divisible by $D$,
--   $$\sum_{x \in o \cdot G} f(d_{\mathcal S}(o, x))\, \check\upsilon_n(\{g \in G_\omega : (g, x) \notin \mathcal H^b\}) \le C\,2^n f(2^{n+2k_n}).$$
--   Here $o = 1^\infty$, the sum is over the orbit (`orbitOne`), $d_{\mathcal S}$ is the Schreier distance (`schreierDist`), $\mathcal H^b$ is `letterGerms ω .b`, and $\check\upsilon_n(\cdot)$ is the mass (`mass`) of $\check\upsilon_n$ (`upsilonCheck`) restricted to $G_\omega$.
--
--   Erschler and Zheng, p. 43, Proposition 7.12: “Let $\upsilon_n$ be defined as in (7.10) and $o = 1^\infty$. Let $f : \mathbb R_+ \to \mathbb R_+$ be a non-increasing function such that there exists constants $D' \in (D, \infty)$, $\frac{f(2x)}{f(x)} \geqslant 2^{-\frac1{D'}}$ for all $x \geqslant 1$. Then there exists a constant $C = C(D') < \infty$ such that $\sum_{x \in o \cdot G} f(d_{\mathcal S}(o, x))\,\upsilon_n(\{g \in G : (g, x) \notin \mathcal H^b\}) \leqslant C2^nf(2^{n+2k_n})$. The same inequality holds with $\upsilon_n$ replaced by $\check\upsilon_n$.”
--
--   The statement is the negation of the last sentence, the $\check\upsilon_n$ inequality as printed, with the encodings of the milestone `ErschlerZheng.tsum_f_mul_mass_upsilon_and_upsilonCheck_not_mem_letterGerms_le`, which states the corrected inequality (the sum over $x \neq o$). The standing assumptions are those of §7.2 (pp. 35 and 40).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 43, Proposition 7.12 for the inverse measures as printed (fails at x = o)

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem not_forall_tsum_f_mul_mass_upsilonCheck_not_mem_letterGerms_le :
    ¬ ∀ (D : ℕ) (ω : ℕ → Fin 3), SatisfiesFr D ω → ∀ k : ℕ → ℕ, IsAdmissibleSeq D k →
      ∀ D' : ℝ, (D : ℝ) < D' →
      ∃ C : ℝ, ∀ f : ℝ → ℝ, (∀ s, 0 ≤ s → 0 ≤ f s) → AntitoneOn f (Set.Ici 0) →
        (∀ s, 1 ≤ s → (2 : ℝ) ^ (-1 / D') ≤ f (2 * s) / f s) → ∀ n, D ∣ n →
          ∑' x : orbitOne ω, f (schreierDist ω oneRay x) *
              mass (fun g : grigorchuk ω => upsilonCheck D ω k n g)
                {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b} ≤
            C * 2 ^ n * f (2 ^ (n + 2 * k n)) := by
  sorry

end ErschlerZheng
