-- Prove2me | Theorems.Thm_EffRobustLearn_eq_A_3
-- name    : EffRobustLearn.eq_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:37:46.789803+00:00
-- url     : https://prove2.me/theorems/5128c90b-44c8-45e0-9eb6-f6c9158f392c
-- title:
--   Eq. (A.3) — the certificate of Definition 3.3 in explicit form
-- statement:
--   Let $c$ be a concept, $\bar\mu:X\to[-1,1]$, and let $\bar S_{\mathrm{inp}},S_{\mathrm{ref}}$ be nonempty. Then the probabilities defining the corruption certificate equal the explicit expression:
--   $$\Pr_{(x,y)\sim\bar S_{\mathrm{inp}}}[c(x)\ne y\text{ or }\mathrm{Rad}(f_{c,\bar\mu}(x))=1]-\Pr_{x\sim S_{\mathrm{ref}}}[\mathrm{Rad}(f_{c,\bar\mu}(x))=1]=\frac1{2|\bar S_{\mathrm{inp}}|}\sum_{(x,y)\in\bar S_{\mathrm{inp}}}\frac{|\bar\mu(x)|+y\bar\mu(x)-2yc(x)}{2+|\bar\mu(x)|+y\bar\mu(x)}-\frac1{2|S_{\mathrm{ref}}|}\sum_{x\in S_{\mathrm{ref}}}\frac{c(x)\bar\mu(x)-1}{1+|\bar\mu(x)|}.$$
--
--   This turns the certificate into a closed form that is affine in $c$, which the whole optimization analysis uses.
--
--   Differences from the source:
--   - generalization: $c\in C$, $\bar\mu\in\mathrm{conv}(C)$ → every Boolean $c$, every $[-1,1]$-valued $\bar\mu$; reason: the identity uses neither membership; it specializes to the source's pairs
--   - encoding: concepts and labels in $\{\pm1\}$; samples as sets of instances → Bool values read through pm; samples as indexed families; reason: same instances; §2's sample conventions keep repeated entries distinct
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), eq. (A.3), p.30 (PDF p.31), with (A.1), (A.2)

import Mathlib
import Definitions.Def_EffRobustLearn_certificate
import Definitions.Def_EffRobustLearn_certificateProb

namespace EffRobustLearn

/-- Eq. (A.3), p.30 (arXiv:2609.17655, held version, sha256 312a0857…): the probabilities of Definition 3.3 equal the explicit form.

**Formalization Note.** Stated for every Boolean `c` and every `[-1, 1]`-valued `μ̄`, which contains the paper's `c ∈ C`, `μ̄ ∈ conv(C)`. -/
theorem eq_A_3 {X : Type*} {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (c : X → Bool) (μ : X → ℝ)
    (hμ : ∀ x, |μ x| ≤ 1) (Sinp : Fin n → X × Bool) (Sref : Fin m → X) :
    certificateProb c μ Sinp Sref = certificate (toPM c) μ Sinp Sref := by sorry

end EffRobustLearn
