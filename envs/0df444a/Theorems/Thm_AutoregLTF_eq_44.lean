-- Prove2me | Theorems.Thm_AutoregLTF_eq_44
-- name    : AutoregLTF.eq_44
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:55:01.561665+00:00
-- url     : https://prove2.me/theorems/977dfca9-458a-4cc1-8f70-1352398ccb1a
-- title:
--   (44), proof of Lemma 3, p.13 — the prompt $x^{i,s}$ outputs $\lambda_{i,s}$: $f^T_w(x^{i,s})=(E^t_i)_{\pi(\mathrm{out},s)}=f^t_{\theta,i,\mathrm{out},s}=\lambda_{i,s}$
-- statement:
--   Let $m\ge2$, $d\ge p+1$ and $T\ge(m+3)p$. Let $\lambda\in\{0,1\}^{m\times m}$ be a labeling with encoding $\theta$, let $B>0$ and $a_1,\dots,a_{p+1}$ be as in Lemma 2 for $\theta$, and let $w$ be the weights (36). For $i,s\in[m]$ let $x^{i,s}$ be the label-free prompt (35), $r_s=(\pi(\mathrm{out},s)-T+1)\bmod p$, and $t=1+(T+r_s-1-\pi(\mathrm{out},s))/p$ as in (43). Then
--
--   $$f^T_w(x^{i,s})=(E^t_{\theta,i})_{\pi(\mathrm{out},s)}=f^t_{\theta,i,\mathrm{out},s}=\lambda_{i,s}.$$
--
--   One common weight vector $w$ makes each of the $m^2$ prompts output its own label at the same time $T$.
--
--   Differences from the source:
--   - encoding: a labeling λ ∈ {0,1}^{m×m} → lab : ℕ → ℕ → Bool, read only at i, j ∈ [m]; reason: every m×m matrix extends to such a function and the statement reads only the entries in [m]×[m]; same instances
--   - encoding: "Take B, a_1, …, a_{p+1} from Lemma 2" → hypotheses B > 0 and the generation property of Lemma 2 for θ = enc m lab; reason: Lemma 2 is existential; the proof uses only these properties of B and a
--   - encoding: the prompts x^{i,s} built from E^0_{θ,i}, E^1_{θ,i} "for each fixed encoding θ" → prompt m d T i s, built from the blocks of the all-zero labeling; reason: by Lemma 1 the blocks E^0, E^1 are the same for every labeling, so these are the paper's prompts
--   - encoding: t := 1 + (T + r_s − 1 − π(out, s))/p, an integer by (34) → the same expression in ℤ, converted to ℕ; reason: the numerator is ≥ T − p ≥ 0 and divisible by p; same value
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), proof of Lemma 3, (44), p.13 (with (34) p.12 and (43) p.13)

import Mathlib
import Definitions.Def_AutoregLTF_gen16
import Definitions.Def_AutoregLTF_prompt

namespace AutoregLTF

/-- **Proof of Lemma 3, (44)**, p.13 (PDF p.13).

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e).

Let `d ≥ p + 1` and `T ≥ (m + 3)p`. Fix a labeling `λ` with encoding `θ`, take `B > 0` and
`a_1, …, a_{p+1}` as in Lemma 2, and let `w` be the weights (36). For `i, s ∈ [m]`, with `r_s` of (34)
and `t := 1 + (T + r_s − 1 − π(out, s))/p` of (43),
`f^T_w(x^{i,s}) = (E^t_i)_{π(out,s)} = f^t_{θ,i,out,s} = λ_{i,s}`, where `x^{i,s}` is the label-free prompt
(35).

**Formalization Note.** `m ≥ 2` is the standing assumption (p.4). "Take `B, a_1, …, a_{p+1}` from
Lemma 2" is the hypothesis `ha`. The prompts `prompt m d T i s` are built from the blocks of the
all-zero labeling, which by Lemma 1 equal `E^0_{θ,i}`, `E^1_{θ,i}` for every `θ` (paper: "the inputs do
not depend on `λ`"). The `t` of (43) is computed in `ℤ` (its numerator is at least `T − p ≥ 0` and is
divisible by `p`, by (34)) and converted to `ℕ`. -/
theorem eq_44 (m : ℕ) (hm : 2 ≤ m) (lab : ℕ → ℕ → Bool) (d : ℕ) (hd : p m + 1 ≤ d)
    (T : ℕ) (hT : (m + 3) * p m ≤ T) (B : ℤ) (hB : 0 < B) (a : ℕ → ℤ)
    (ha : ∀ i ∈ Finset.Icc 1 m, ∀ t : ℕ, ∀ r < p m,
      gen16 (p m) B a (hist m (enc m lab) i t) (p m + 1 + r) = E m (enc m lab) i (t + 1) r)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 m) (s : ℕ) (hs : s ∈ Finset.Icc 1 m) :
    let t : ℕ := (1 + ((T : ℤ) + rs m T s - 1 - piOut m s) / (p m : ℤ)).toNat
    ltf d T (wOf d (p m) B a) (prompt m d T i s) = E m (enc m lab) i t (piOut m s) ∧
    E m (enc m lab) i t (piOut m s) = (state m (enc m lab) i t).out s ∧
    (state m (enc m lab) i t).out s = lab i s := by sorry

end AutoregLTF
