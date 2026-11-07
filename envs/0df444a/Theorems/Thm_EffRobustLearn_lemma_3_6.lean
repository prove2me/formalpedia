-- Prove2me | Theorems.Thm_EffRobustLearn_lemma_3_6
-- name    : EffRobustLearn.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:37:45.973908+00:00
-- url     : https://prove2.me/theorems/c7f35362-c89e-415f-b4f2-b5b2340a500e
-- title:
--   Lemma 3.6 — the iteration objective is affine in the concept
-- statement:
--   Let $\bar\mu,h:X\to\mathbb R$ be fixed and let $\bar S_{\mathrm{inp}},S_{\mathrm{ref}}$ be nonempty. There is a constant $C_t\in\mathbb R$ such that, for every $c:X\to\mathbb R$,
--   $$\widehat{\mathrm{err}}_{S_{\mathrm{ref}}}(h,c)-\eta(c,\bar\mu;\bar S_{\mathrm{inp}},S_{\mathrm{ref}})=C_t+\langle g,c[S]\rangle,$$
--   where $g$ is the vector (3.6) of $\bar\mu$ and $h$.
--
--   This reduces each round to a linear objective over $K$.
--
--   Differences from the source:
--   - generalization: $c\in C$; $\bar\mu_t\in\mathrm{conv}(C)$; $h_t=\mathrm{maj}_k\circ\bar\mu_t$ → every real-valued $c$, $\bar\mu$ and $h$; reason: the identity needs only $y^2=1$; real-valued $c$ is the affine extension (3.7), and the source's triples are instances
--   - encoding: exists $g_t$ with (3.6) → $g$ is the explicit vector (3.6); reason: the source's displayed vector is the witness
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Lemma 3.6, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_EffRobustLearn_errD
import Definitions.Def_EffRobustLearn_certificate
import Definitions.Def_EffRobustLearn_gVec

namespace EffRobustLearn

/-- Lemma 3.6 (Linearization), p.15 (arXiv:2609.17655, held version, sha256 312a0857…): for fixed `μ̄` and `h` there is a constant `C_t` with
`err̂_{Sref}(h, c) - η(c, μ̄; S̄inp, Sref) = C_t + ⟨g, c[S]⟩`, `g` being the paper's vector (3.6).

**Formalization Note.** The identity is stated for every real-valued `c` and arbitrary `μ̄`, `h`. That contains the paper's `c ∈ C`,
`μ̄_t ∈ conv(C)` and `h_t = maj_k ∘ μ̄_t`, and it is the affine extension (3.7). -/
theorem lemma_3_6 {X : Type*} {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (μ h : X → ℝ)
    (Sinp : Fin n → X × Bool) (Sref : Fin m → X) :
    ∃ Ct : ℝ, ∀ c : X → ℝ,
      errHat Sref h c - certificate c μ Sinp Sref =
        Ct + inner ℝ (gVec μ h Sinp Sref) (evalVec c Sinp Sref) := by sorry

end EffRobustLearn
