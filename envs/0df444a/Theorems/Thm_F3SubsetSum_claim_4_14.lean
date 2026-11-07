-- Prove2me | Theorems.Thm_F3SubsetSum_claim_4_14
-- name    : F3SubsetSum.claim_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:39.745933+00:00
-- url     : https://prove2.me/theorems/86c5bc48-7c00-4547-9ab1-bd044608c958
-- title:
--   Claim 4.14 — $W_t=\ker(C_{L_t}|_{W_{t-1}})$ and $X_t=\operatorname{rank}(C_{L_t}|_{W_{t-1}})$
-- statement:
--   Let $q\ge3$ be prime and $D\ge2$. For a history $a_1,\dots,a_{t-1}$ and a new sample $a_t$, let $V_{t-1}\subseteq V_t\subseteq R_D$ be the sample images (39), $W_s=V_s^\perp\subseteq R_D^*$ their annihilators, and $C_{L_t}:R_D^*\to R_{D-2}^*$ the contraction by $L_t=\langle a_t,x\rangle$. Then
--
--   $$W_t=\ker\bigl(C_{L_t}|_{W_{t-1}}\bigr)\qquad\text{and}\qquad X_t=\operatorname{rank}\bigl(C_{L_t}|_{W_{t-1}}\bigr).$$
--
--   This moves the martingale step into the dual space, where it becomes a rank question.
--
--   Differences from the source:
--   - encoding: the standing integer D ≥ 2 of §4.1 (eq. (29), p.18), left implicit in the statement → hypothesis D ≥ 2; reason: R*_{D−2} is undefined for D < 2 (natural-number subtraction would make it R*_0)
--   - encoding: ker(C_{L_t}|_{W_{t−1}}) as a subspace of R*_D → the kernel, a subspace of W_{t−1}, mapped into R*_D by the inclusion; reason: the paper identifies the two
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Claim 4.14, p.25

import Mathlib
import Definitions.Def_F3SubsetSum_TruncatedRing
import Definitions.Def_F3SubsetSum_SampleImage
import Definitions.Def_F3SubsetSum_SymbolicRank

namespace F3SubsetSum

/-- **Claim 4.14** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, Claim 4.14, p.25):
"Let C_{L_t}|_{W_{t−1}} : W_{t−1} → R*_{D−2} be the restriction of C_{L_t} to W_{t−1}. Then
W_t = ker(C_{L_t}|_{W_{t−1}}) and X_t = rank(C_{L_t}|_{W_{t−1}})."

Over `F_q`, `q ≥ 3` prime, `D ≥ 2`: for a history `a_1, …, a_{t−1}` and a new sample `a_t`, with
`V_{t−1}`, `V_t` the sample images (39) and `W = V^⊥ ⊆ R*_D` their annihilators (p.24): `W_t` is
the kernel of the contraction `C_{L_t}` (p.25) restricted to `W_{t−1}`, viewed inside `R*_D`, and
the increment `X_t` (40) is the rank of that restriction.

**Formalization Note** The kernel, a subspace of `W_{t−1}`, is mapped into `R*_D` by the
inclusion. -/
theorem claim_4_14 (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (n D : ℕ) (hD : 2 ≤ D) {t : ℕ}
    (a : Fin t → Fin n → ZMod q) (a' : Fin n → ZMod q) :
    (sampleImage q (Fin.snoc a a') D).dualAnnihilator =
        (LinearMap.ker ((contraction (ZMod q) n q D a').domRestrict
            (sampleImage q a D).dualAnnihilator)).map
          (sampleImage q a D).dualAnnihilator.subtype ∧
      increment q a a' D =
        Module.finrank (ZMod q) (LinearMap.range ((contraction (ZMod q) n q D a').domRestrict
          (sampleImage q a D).dualAnnihilator)) := by sorry

end F3SubsetSum
