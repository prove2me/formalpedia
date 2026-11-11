-- Prove2me | Theorems.Thm_CubicPermFPRAS_lemma_14
-- name    : CubicPermFPRAS.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:46.37625+00:00
-- url     : https://prove2.me/theorems/5a9fcc0e-75ea-45ff-94cb-575560ea12ce
-- title:
--   Lemma 14, p.14 — the assignment Glauber dynamics has spectral gap at least $1$
-- statement:
--   Let $B$ be an $n\times n$ matrix with positive entries and rows summing to $1$, $J\ge0$ and $a>0$. For every $f:\Omega_{\mathrm{aux}}\to\mathbb R$,
--   $$\mathrm{Var}_{\nu_a}(f)\le\langle f,L_af\rangle_{\nu_a},$$
--   that is, the assignment Glauber dynamics has spectral gap at least $1$.
--
--   Consequently $O(\log n)$ units of continuous time suffice from a warm start at each stage of the sampler.
--
--   Differences from the source:
--   - generalization: the rescaled matrix $B$ of Eq. (10) and $J=J_\alpha n^2$ → every matrix $B$ with positive entries and rows summing to $1$, and every $J\ge0$; reason: the rescaled matrix is such a matrix; the proofs (§8.2–8.3) use only these properties
--   - encoding: spectral gap at least $1$ → the Poincaré inequality $\mathrm{Var}_{\nu_a}(f)\le\langle f,L_af\rangle_{\nu_a}$; reason: for a reversible chain the spectral gap is the best constant in this inequality
--   - encoding: an $n\times n$ instance ($V_1$, $V_2$ of size $n$) → the hypothesis $1\le n$; reason: the paper's vertex classes $V_1,V_2$ are nonempty throughout (an anchor $r\in V_1$ exists); $n=0$ is no instance of the source
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Lemma 14, p.14 (PDF 16); proof, p.50 (PDF 52)

import Mathlib
import Definitions.Def_CubicPermFPRAS_nuAux

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **Lemma 14** (spectral gap of the assignment Glauber dynamics), p.14 (PDF 16), X. Chen, H. Guo, E. Vigoda, X. Yang, *An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717 (held version, sha256 9e14f335…);
proved on p.50 (PDF 52).

The assignment Glauber dynamics has spectral gap at least `1`: for every `f : Ω_aux → ℝ`,
`Var_{ν_a}(f) ≤ ⟨f, L_a f⟩_{ν_a}`.

**Formalization Note.** The spectral gap of the reversible continuous-time chain with positive
Laplacian `L_a` is stated in its Poincaré form. Stated for every `a > 0`, every matrix `B` with
positive entries and rows summing to `1`, and every `J ≥ 0` (the paper fixes `J = J_α n²`). -/
theorem lemma_14 (n : ℕ) (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ) (hB : ∀ u v, 0 < B u v)
    (hrow : ∀ u, ∑ v, B u v = 1) (J : ℝ) (hJ : 0 ≤ J) (a : ℝ) (ha : 0 < a) (f : Asg n → ℝ) :
    ∑ σ, nuAux B J a σ * f σ ^ 2 - (∑ σ, nuAux B J a σ * f σ) ^ 2 ≤
      ∑ σ, nuAux B J a σ * f σ * (glauberLap B J a).mulVec f σ := by sorry

end CubicPermFPRAS
