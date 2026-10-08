-- Prove2me | Theorems.Thm_ErschlerZheng_tsum_f_mul_mass_upsilon_and_upsilonCheck_not_mem_letterGerms_le
-- name    : ErschlerZheng.tsum_f_mul_mass_upsilon_and_upsilonCheck_not_mem_letterGerms_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T08:49:22.7254+00:00
-- url     : https://prove2.me/theorems/c7b3368a-5992-496d-b4b7-6aae38847d40
-- title:
--   Proposition 7.12, corrected — for non-increasing f ⩾ 0 with f(2s)/f(s) ⩾ 2^{−1/D′} (D′ > D), Σ_x f(d_𝒮(o, x)) υ_n{g : (g, x) ∉ ℋ^b} ⩽ C 2^n f(2^{n+2k_n}), and likewise for υ̌_n summed over x ≠ o
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $(k_n)$ satisfy the standing assumption of p. 40 (`IsAdmissibleSeq`), and let $D' > D$ be real. Then there is a constant $C$ such that for every $f : \mathbb R \to \mathbb R$ that is non-negative and non-increasing on $[0, \infty)$ (`AntitoneOn f (Set.Ici 0)`) with $f(2s)/f(s) \ge 2^{-1/D'}$ for all $s \ge 1$, and every $n$ divisible by $D$, the family $x \mapsto f(d_{\mathcal S}(o, x))\, \upsilon_n(\{g \in G_\omega : (g, x) \notin \mathcal H^b\})$ on $o \cdot G$ is summable and
--   $$\sum_{x \in o \cdot G} f(d_{\mathcal S}(o, x))\, \upsilon_n(\{g \in G_\omega : (g, x) \notin \mathcal H^b\}) \le C\,2^n f(2^{n+2k_n}),$$
--   and the same, summability and bound, with $\upsilon_n$ replaced by $\check\upsilon_n$ (`upsilonCheck`) and $x$ ranging over $o \cdot G$, $x \neq o$. Here $o = 1^\infty$, the sum is over the orbit (`orbitOne`), $d_{\mathcal S}$ is the Schreier distance (`schreierDist`), $\mathcal H^b$ is `letterGerms ω .b`, and $\upsilon_n(\cdot)$ is the mass (`mass`) of $\upsilon_n$ (`upsilon`) restricted to $G_\omega$.
--
--   Erschler and Zheng, p. 43, Proposition 7.12: “Let $\upsilon_n$ be defined as in (7.10) and $o = 1^\infty$. Let $f : \mathbb R_+ \to \mathbb R_+$ be a non-increasing function such that there exists constants $D' \in (D, \infty)$, $\frac{f(2x)}{f(x)} \geqslant 2^{-\frac1{D'}}$ for all $x \geqslant 1$. Then there exists a constant $C = C(D') < \infty$ such that $\sum_{x \in o \cdot G} f(d_{\mathcal S}(o, x))\,\upsilon_n(\{g \in G : (g, x) \notin \mathcal H^b\}) \leqslant C2^nf(2^{n+2k_n})$. The same inequality holds with $\upsilon_n$ replaced by $\check\upsilon_n$.”
--
--   *Correction.* The $\check\upsilon_n$ inequality as printed, summed over all of $o \cdot G$, is false at its term $x = o$ ([`ErschlerZheng.not_forall_tsum_f_mul_mass_upsilonCheck_not_mem_letterGerms_le`](https://prove2.me/theorems/27dd9aff-ec7c-4d59-9d7e-0931e9cb8e9e)). The $\upsilon_n$ inequality is stated as printed, over all of $o \cdot G$. The paper's application, the proof of Theorem 7.13 (p. 43), takes $f(s) = C\bigl(\frac{s}{\log_2^{2A} s}\bigr)^{\beta-1}(\log_2 s)^{-\frac{1-\beta}{1+\beta}(\frac{2A}D-\epsilon)}$, which is not defined at $s = 0$.
--
--   A function $\mathbb R_+ \to \mathbb R_+$ is a real function whose conditions are asked on $[0, \infty)$. $D'$ is fixed before the constant, as $C = C(D')$ indicates, and the constant is chosen before $f$ and $n$; it is chosen after $\omega$ and $(k_n)$, which are fixed throughout §7. The ratio condition forces $f(s) > 0$ for $s \ge 1$, as the printed quotient presupposes. The sums are asserted to converge, as the printed inequality presupposes. The standing assumptions are those of §7.2 (pp. 35 and 40).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 43, Proposition 7.12, corrected

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem tsum_f_mul_mass_upsilon_and_upsilonCheck_not_mem_letterGerms_le (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (D' : ℝ) (hD' : (D : ℝ) < D') :
    ∃ C : ℝ, ∀ f : ℝ → ℝ, (∀ s, 0 ≤ s → 0 ≤ f s) → AntitoneOn f (Set.Ici 0) →
      (∀ s, 1 ≤ s → (2 : ℝ) ^ (-1 / D') ≤ f (2 * s) / f s) → ∀ n, D ∣ n →
        Summable (fun x : orbitOne ω => f (schreierDist ω oneRay x) *
            mass (fun g : grigorchuk ω => upsilon D ω k n g)
              {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b}) ∧
        ∑' x : orbitOne ω, f (schreierDist ω oneRay x) *
            mass (fun g : grigorchuk ω => upsilon D ω k n g)
              {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b} ≤
          C * 2 ^ n * f (2 ^ (n + 2 * k n)) ∧
        Summable (fun x : ↥(orbitOne ω \ {oneRay}) => f (schreierDist ω oneRay x) *
            mass (fun g : grigorchuk ω => upsilonCheck D ω k n g)
              {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b}) ∧
        ∑' x : ↥(orbitOne ω \ {oneRay}), f (schreierDist ω oneRay x) *
            mass (fun g : grigorchuk ω => upsilonCheck D ω k n g)
              {g | ((g : Garrido.BinaryTreeAut), (x : Ray)) ∉ letterGerms ω .b} ≤
          C * 2 ^ n * f (2 ^ (n + 2 * k n)) := by
  sorry

end ErschlerZheng
