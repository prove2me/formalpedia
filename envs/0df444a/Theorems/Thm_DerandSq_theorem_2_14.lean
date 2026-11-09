-- Prove2me | Theorems.Thm_DerandSq_theorem_2_14
-- name    : DerandSq.theorem_2_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:06:39.543182+00:00
-- url     : https://prove2.me/theorems/8e24f8fe-0b7b-42c7-b8d1-bd5e50ba48f5
-- title:
--   Theorem 2.14 ([BC19], Bordenave–Collins) — strong convergence of uniform permutation and matching matrices
-- statement:
--   Let $D, r, s \in \mathbb N$ and $\varepsilon > 0$. Let $g_1, \dots, g_r$ freely generate the free group $F_r$, let $h_1, \dots, h_s$ be the canonical involutive generators of $\Gamma_s = \mathbb Z_2^{*s}$, and set $u_i = \lambda(g_i)$ (2.10), $m_j = \lambda(h_j)$ (2.11), where $u$ and $m$ together freely generate $F_r * \Gamma_s$.
--
--   1. For every $N$, let $U^N = (U^N_1, \dots, U^N_r)$ be i.i.d. uniformly random $N \times N$ permutation matrices. For every $P \in M_D(\mathbb C) \otimes \mathbb C^*\langle x_1, \dots, x_r\rangle$,
--   $$
--   \mathbb P\Bigl[\,\bigl|\,\|P(U^N)|_{\perp 1}\| - \|P(u)\|_{C^*_{\mathrm{red}}(F_r)}\bigr| \geq \varepsilon\Bigr] = o_N(1).
--   $$
--   2. For even $N$, let moreover $M^N = (M^N_1, \dots, M^N_s)$ be i.i.d. uniformly random matching matrices, independent of $U^N$. For every $P \in M_D(\mathbb C) \otimes \mathbb C^*\langle x_1, \dots, x_r, y_1, \dots, y_s\rangle$,
--   $$
--   \mathbb P\Bigl[\,\bigl|\,\|P(U^N, M^N)|_{\perp 1}\| - \|P(u, m)\|_{C^*_{\mathrm{red}}(F_r * \Gamma_s)}\bigr| \geq \varepsilon\Bigr] = o_N(1). \tag{2.12}
--   $$
--
--   Here $Y|_{\perp 1} = (I_D \otimes (I - J))Y(I_D \otimes (I - J))$ with $J = \mathbf 1\mathbf 1^\top/N$. This is the transfer principle of the proof of Theorem 4.1: norms of fixed polynomials in random permutations and matchings converge in probability to the norms of the same polynomials in the free generators.
--
--   Differences from the source:
--   - reading: iid uniformly random matching matrices (footnote 1: permutation matrices of involutions) → uniform perfect matchings PM (fixed-point-free involutions) of Fin N; reason: the Bordenave–Collins matching model; Theorem 1.1 says "perfect matching", and even N is only needed for perfect matchings
--   - reading: for all ε > 0 (stated in the first display, ε also in (2.12)) → one ε > 0 quantified for both displays; reason: the second display is stated under the same quantifier
--   - encoding: o_N(1) → Tendsto … atTop (𝓝 0), over all N in 1. and over N = 2n in 2.; reason: the meaning of o_N(1) along the stated N
--   - encoding: independent uniform tuples U^N, M^N → uniform distribution on (Fin r → Perm (Fin 2n)) × (Fin s → PM 2n); reason: a product of independent uniform laws is the uniform law on the product
--   - encoding: M_D(ℂ) ⊗ ℂ*⟨x⟩, P(U^N), ‖P(u)‖_{C*_red} → NCPoly with letters inl/inr, NCPoly.eval on PiLp 2 copies, operator norm on D copies of ℓ²(Γ); reason: the reduced C*-norm of M_D(C*_red(Γ)) is the operator norm on ℂ^D ⊗ ℓ²(Γ)
--   - encoding: F_r ∗ Γ_s, x_i ↦ u_i, y_j ↦ m_j → Monoid.Coprod (FreeGroup (Fin r)) (Gam s); variables Sum.inl i, Sum.inr j; reason: the free product of groups and its two canonical embeddings
--   - encoding: permutation matrices acting on ℂ^N → permOp, e_v ↦ e_{σ v}; reason: the paper's orientation λ(σ)δ_v = δ_{σv}
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), Theorem 2.14, pp.12–13, and display (2.12), p.13 (with (2.10), (2.11), p.12)

import Mathlib
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_DerandSq_PM
import Definitions.Def_DerandSq_mGen
import Definitions.Def_DerandSq_leftReg
import Definitions.Def_DerandSq_NCPoly_eval
import Definitions.Def_DerandSq_permOp
import Definitions.Def_DerandSq_perpCompress

namespace DerandSq

/-- Theorem 2.14 (Asymptotic Convergence, [BC19], Bordenave–Collins) of Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), pp.12–13, both
displays. Let `D, r, s ∈ ℕ` and `ε > 0`.

1. For every `P ∈ M_D(ℂ) ⊗ ℂ*⟨x_1, …, x_r⟩` and i.i.d. uniform permutation matrices
   `U^N = (U_1^N, …, U_r^N)`,
   `P[ |‖P(U^N)|_{⊥1}‖ − ‖P(u)‖_{C*_red(F_r)}| ≥ ε ] = o_N(1)`, `u_i = λ(g_i)` (2.10).
2. For even `N`, i.i.d. uniform matching matrices `M^N = (M_1^N, …, M_s^N)` independent of
   `U^N`, and every `P ∈ M_D(ℂ) ⊗ ℂ*⟨x_1, …, x_r, y_1, …, y_s⟩`,
   `P[ |‖P(U^N, M^N)|_{⊥1}‖ − ‖P(u, m)‖_{C*_red(F_r ∗ Γ_s)}| ≥ ε ] = o_N(1)` (2.12), with
   `m_j = λ(h_j)` (2.11), `u` and `m` freely generating `F_r ∗ Γ_s`.

**Formalization Note** Permutation and matching matrices act on `ℂ^N` by `e_v ↦ e_{σ v}`;
matchings are perfect matchings (`PM`); the independent uniform tuples are a uniform element of
the product type; `o_N(1)` is the limit `N → ∞` (over all `N` in 1., over `N = 2n` in 2.). The
reduced norm of `P(u)` is the operator norm on `D` copies of `ℓ²(F_r)` (resp. `ℓ²(F_r ∗ Γ_s)`,
`F_r ∗ Γ_s` = `Monoid.Coprod (FreeGroup (Fin r)) (Gam s)`). In the second display the variables
`x_i`, `y_j` are `Sum.inl i`, `Sum.inr j`. -/
theorem theorem_2_14 (D r s : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (∀ P : NCPoly D (Fin r),
      Filter.Tendsto (fun N : ℕ => PunctSketch.coinProb (fun U : Fin r → Equiv.Perm (Fin N) =>
          ε ≤ |‖perpCompress D N (P.eval (fun i => permOp (U i)))‖ -
            ‖P.eval (fun i => leftReg (FreeGroup.of i))‖|))
        Filter.atTop (nhds 0)) ∧
    (∀ P : NCPoly D (Fin r ⊕ Fin s),
      Filter.Tendsto (fun n : ℕ =>
          PunctSketch.coinProb (fun UM : (Fin r → Equiv.Perm (Fin (2 * n))) × (Fin s → PM (2 * n)) =>
            ε ≤ |‖perpCompress D (2 * n)
                  (P.eval (Sum.elim (fun i => permOp (UM.1 i)) (fun j => permOp (UM.2 j).1)))‖ -
              ‖P.eval (Sum.elim
                  (fun i => leftReg (Monoid.Coprod.inl (FreeGroup.of i) :
                    Monoid.Coprod (FreeGroup (Fin r)) (Gam s)))
                  (fun j => leftReg (Monoid.Coprod.inr (mGen j) :
                    Monoid.Coprod (FreeGroup (Fin r)) (Gam s))))‖|))
        Filter.atTop (nhds 0)) := by sorry

end DerandSq
