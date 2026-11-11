-- Prove2me | Theorems.Thm_ChowFormsCH_lemma_4_6
-- name    : ChowFormsCH.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:01:59.321192+00:00
-- url     : https://prove2.me/theorems/eea4e325-619e-48b8-a7a4-27621d94c202
-- title:
--   Lemma 4.6 — the squarefree part of $\mathrm{TT}_t$ of the perturbed resultant is the Chow form of $\lim_{t\to 0} V^p(G)$
-- statement:
--   Let $K$ be algebraically closed, $k\le n$, and $G_1,\dots,G_k\in K[x_0,\dots,x_n]$ forms of degrees $d_i\ge 1$. Let $L_i=u_{i,0}x_0+\dots+u_{i,n}x_n$ for $0\le i\le n-k$ and
--   $$
--   R':=\mathrm{Res}\big((1-t)G_1+tx_1^{d_1},\dots,(1-t)G_k+tx_k^{d_k},L_0,\dots,L_{n-k}\big)\in K[u][t],
--   $$
--   the resultant with respect to $x_0,\dots,x_n$. Then $R'\neq 0$, and if $R$ is the squarefree part of $R'$, the squarefree part of the trailing coefficient $\mathrm{TT}_tR$ (the coefficient of the lowest power of $t$) is a nonzero scalar multiple of the Chow form of $\lim_{t\to 0}V^p(G_1,\dots,G_k)$, in the $n-k+1$ groups of variables $u_0,\dots,u_{n-k}$.
--
--   Even when $V(G_1,\dots,G_k)$ is not equidimensional (so that the unperturbed resultant vanishes), the perturbed resultant is nonzero and its trailing coefficient encodes the limit variety; this is the first step of the construction of Theorem 4.9.
--
--   **Formalization Note** $\mathrm{Res}$ is any polynomial satisfying Definition 2.5 for the degrees $(d_1,\dots,d_k,1,\dots,1)$. "Nonzero scalar multiple of the Chow form" is `IsChowForm`. Squarefree parts are unique up to units, and the claim is made for every choice.
--
--   Differences from the source:
--   - encoding: forms over a field F, varieties over F̄ → an algebraically closed field K (of Type); reason: an instance over F is an instance over K = F̄: the resultant is universal and squarefree parts are compatible with the extension
--   - reading: forms G_i with d_i := deg G_i → G_i homogeneous of degree d_i with d_i ≥ 1; reason: Definition 2.5 fixes positive degrees for the resultant; the zero form is allowed with its formal degree
--   - reading: Let R be the squarefree part of R′ … the squarefree part of TT_t R is a nonzero scalar multiple of the Chow form → R′ ≠ 0, and every squarefree part R of R′ and every squarefree part s of TT_t R satisfy IsChowForm; reason: the conclusion presupposes R′ ≠ 0 (0 has no squarefree part); squarefree parts are unique up to units
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Lemma 4.6, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_ChowFormsCH_limVar
import Definitions.Def_ChowFormsCH_IsChowForm
import Definitions.Def_ChowFormsCH_IsUnivResultant
import Definitions.Def_ChowFormsCH_IsSqfPart

set_option autoImplicit false

namespace ChowFormsCH

/-- **Lemma 4.6** (Andrews–Garg–Oliveira–Schost, *Some algebraic and geometric computations in CH
via Chow forms*, arXiv:2611.05289, held version, sha256 75e796c6…, p.31). Let `G₁, …, G_k` be forms
of degrees `d_i ≥ 1` in `x₀, …, xₙ`, `k ≤ n`, and
`R′ := Res((1 − t)G₁ + t x₁^{d₁}, …, (1 − t)G_k + t x_k^{d_k}, L₀, …, L_{n−k}) ∈ K[u][t]`, the
resultant with respect to `x₀, …, xₙ`, `L_i = u_{i,0}x₀ + ⋯ + u_{i,n}xₙ`. Let `R` be the squarefree
part of `R′`. Then the squarefree part of `TT_t R` is a nonzero scalar multiple of the Chow form of
`lim_{t→0} V^p(G₁, …, G_k)`.

**Formalization Note** `K` is algebraically closed; `Res` is any universal resultant
(`IsUnivResultant`) for the degrees `(d₁, …, d_k, 1, …, 1)`. `TT_t` is `Polynomial.trailingCoeff`
in `K[u][t]`. "Nonzero scalar multiple of the Chow form" is `IsChowForm` (dimension `n − k`). The
statement includes `R′ ≠ 0`, which the conclusion presupposes (a squarefree part of `0` does not
exist); squarefree parts are unique up to units, so the claim is made for every choice. -/
theorem lemma_4_6 {K : Type} [Field K] [IsAlgClosed K] {n k : ℕ} (hk : k ≤ n)
    (G : Fin k → MvPolynomial (Fin (n + 1)) K) (d : Fin k → ℕ)
    (hG : ∀ i, (G i).IsHomogeneous (d i)) (hd : ∀ i, 1 ≤ d i)
    (R : MvPolynomial (ResVar n (perturbedDegrees (n := n) d)) ℤ)
    (hR : IsUnivResultant n (perturbedDegrees (n := n) d) R) :
    resultantOf R (perturbedForms hk G d) ≠ 0 ∧
    ∀ Rsf : TURing n k K, IsSqfPart (resultantOf R (perturbedForms hk G d)) Rsf →
      ∀ s : MvPolynomial (Fin (n - k + 1) × Fin (n + 1)) K, IsSqfPart Rsf.trailingCoeff s →
        IsChowForm (limVar hk G d 0) (n - k) s := by sorry

end ChowFormsCH
