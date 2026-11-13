-- Prove2me | Theorems.Thm_AutoregLTF_eq_39
-- name    : AutoregLTF.eq_39
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:55:32.098313+00:00
-- url     : https://prove2.me/theorems/e6e12180-6f33-462f-bcde-5ce126ffa62c
-- title:
--   (39), proof of Lemma 3, p.13 — the trajectory from $0^{d-p}E^0_i$ passes through the blocks: $(z^{(i)}_{(t-1)p},\dots,z^{(i)}_{tp})=(0,E^t_i)$
-- statement:
--   Let $m\ge2$, $d\ge p+1$, and let $\lambda\in\{0,1\}^{m\times m}$ be a labeling with encoding $\theta$. Let $B>0$ and $a_1,\dots,a_{p+1}$ be as in Lemma 2 for $\theta$, i.e. for every $i\in[m]$ and $t\ge0$ the history $(0,E^t_{\theta,i})$ generates $E^{t+1}_{\theta,i}$ under (16). Let $w_\ell=a_\ell/B$ for $\ell\le p+1$ and $w_\ell=0$ for $p+1<\ell\le d$ (36), and let $z^{(i)}$ be the trajectory of (1) with these weights from the prompt $(z^{(i)}_{1-d},\dots,z^{(i)}_0)=0^{d-p}E^0_{\theta,i}$. Then for every $i\in[m]$ and $t\ge0$
--
--   $$\big(z^{(i)}_{(t-1)p},\dots,z^{(i)}_{tp}\big)=\big(0,E^t_{\theta,i}\big).$$
--
--   So the free-running autoregressive LTF writes the blocks $E^0_i,E^1_i,E^2_i,\dots$ one after another.
--
--   Differences from the source:
--   - encoding: a labeling λ ∈ {0,1}^{m×m} → lab : ℕ → ℕ → Bool, read only at i, j ∈ [m]; reason: every m×m matrix extends to such a function and the statement reads only the entries in [m]×[m]; same instances
--   - encoding: "Take B, a_1, …, a_{p+1} from Lemma 2" → hypotheses B > 0 and the generation property of Lemma 2 for θ = enc m lab; reason: Lemma 2 is existential; the proof uses only these properties of B and a
--   - encoding: the tuple equality (z_{(t−1)p}, …, z_{tp}) = (0, E^t_i) → z_{(t−1)p} = 0 and z_{(t−1)p+1+r} = E^t_{i,r} for 0 ≤ r < p; reason: entrywise form of the same equality
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), proof of Lemma 3, (39), p.13 (with (36)–(38), p.12)

import Mathlib
import Definitions.Def_AutoregLTF_gen16
import Definitions.Def_AutoregLTF_prompt

namespace AutoregLTF

/-- **Proof of Lemma 3, (39)**, p.13 (PDF p.13).

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e).

Fix a labeling `λ` with encoding `θ`, take `B > 0` and `a_1, …, a_{p+1}` as in Lemma 2, let `w` be the
weights (36) (`w_ℓ = a_ℓ/B` for `ℓ ≤ p + 1`, `0` otherwise), and let `z^{(i)}` be the trajectory of (1)
with these weights from the prompt `(z^{(i)}_{1−d}, …, z^{(i)}_0) = 0^{d−p} E^0_{θ,i}` (37)–(38). If
`d ≥ p + 1`, then for every `i ∈ [m]` and `t ≥ 0`,
`(z^{(i)}_{(t−1)p}, …, z^{(i)}_{tp}) = (0, E^t_{θ,i})`.

**Formalization Note.** `m ≥ 2` is the standing assumption (p.4). "Take `B, a_1, …, a_{p+1}` from
Lemma 2" is the hypothesis `ha`: `B > 0` and, for every `i ∈ [m]` and `t`, the history
`(0, E^t_{θ,i})` generates `E^{t+1}_{θ,i}` under (16). `zAt w x n` is `z_n` of (1) with the paper's indices
(`n ≥ 1 − d`); the tuple equality is stated entrywise. -/
theorem eq_39 (m : ℕ) (hm : 2 ≤ m) (lab : ℕ → ℕ → Bool) (d : ℕ) (hd : p m + 1 ≤ d)
    (B : ℤ) (hB : 0 < B) (a : ℕ → ℤ)
    (ha : ∀ i ∈ Finset.Icc 1 m, ∀ t : ℕ, ∀ r < p m,
      gen16 (p m) B a (hist m (enc m lab) i t) (p m + 1 + r) = E m (enc m lab) i (t + 1) r)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 m) (t : ℕ) :
    zAt (wOf d (p m) B a) (prompt0 m d (enc m lab) i) (((t : ℤ) - 1) * p m) = false ∧
    ∀ r < p m, zAt (wOf d (p m) B a) (prompt0 m d (enc m lab) i)
      (((t : ℤ) - 1) * p m + 1 + r) = E m (enc m lab) i t r := by sorry

end AutoregLTF
