-- Prove2me | Theorems.Thm_BetheKS_ref12_corollary_3_4
-- name    : BetheKS.ref12_corollary_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:45.827203+00:00
-- url     : https://prove2.me/theorems/40e3b107-58eb-440e-921e-dac27ecc73b1
-- title:
--   [12, Cor. 3.4] (negative-outlier bound), as used on p.25 — at most $r_\pm$ eigenvalues of $H(\pm t,G_n)$ below $-\varepsilon$
-- statement:
--   This is a result of the companion paper D. Dong, T. McKenzie, *The Bethe–Hessian down to the percolation threshold*, arXiv:2608.16672, Corollary 3.4, stated as the present paper invokes it. Fix a sign $s\in\{\pm1\}$ and $t\ge\sqrt d$ with $t<|\mu|$ for every informative eigenvalue $\mu$ of sign $s$ (§7). For every $\varepsilon>0$, with probability tending to one,
--   $$
--   \#\{\lambda\in\sigma(H(st,G_n)):\lambda<-\varepsilon\}\ \le\ r_s,
--   $$
--   eigenvalues counted with multiplicity, where $r_{+1}=r_+$ and $r_{-1}=r_-$. In the proof of Proposition 7.2 it gives $\sum_\mu\operatorname{rank}P_{\mu,n}\le\#\{\lambda\in\sigma(H_n):\lambda<-\varepsilon\}\le r_+$; the negative sign is used in the proof of Theorem 2.2.
--
--   Differences from the source:
--
--   - reading: 'Choose ε > 0 so that every I_μ lies below −ε' and the bound for that ε → the bound for every ε > 0; reason: γ in the proof is arbitrary, so every small ε is used; this is the usual form of a negative-outlier bound
--   - reading: [12, Corollary 3.4] for H_n = H(t, G_n), and the corresponding negative-outlier count for H(−t, G_n) → both signs, at every t of the §7 range; reason: as the paper invokes it on p.25 and p.12; [12]'s own hypotheses are not printed here
--   - encoding: n → ∞ with |σ⁻¹(i)| = π_i n → n → ∞ along 𝒩_π = {n : π_i n ∈ ℕ ∀ i}, for every sequence of exact-size label maps σ_n; reason: the paper's deterministic community-size convention (p.4); the statement is uniform over the labelings
--   - encoding: π a distribution on [r] → every π_a > 0; reason: the r eigenfunctions orthonormal in L²(π) that the paper uses exist only then; excludes undefined cases
--   - encoding: edge probability P_{σ(u)σ(v)}/n → min(1, P_{σ(u)σ(v)}/n); reason: affects only finitely many n, not the limits
--   - encoding: eigenvalues of Q counted with multiplicity → real roots of the characteristic polynomial of Q, with multiplicity; reason: Q is diagonalizable with real spectrum, so algebraic and geometric multiplicities agree
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Proof of Proposition 7.2, p.25 (PDF p.26), citing [12, Corollary 3.4]

import Mathlib
import Definitions.Def_BetheKS_sbmProb
import Definitions.Def_BetheKS_betheHessian

set_option autoImplicit false

namespace BetheKS

/-- **[12, Corollary 3.4] (negative-outlier bound), as used on p.25** — Dong, McKenzie,
arXiv:2610.41802 (held version, sha256 4da41e16…), proof of Proposition 7.2, p.25 (PDF p.26),
citing D. Dong, T. McKenzie, *The Bethe–Hessian down to the percolation threshold*,
arXiv:2608.16672, Corollary 3.4: "The negative-outlier bound of [12, Corollary 3.4] gives, with
probability tending to one, `∑_µ rank P_{µ,n} ≤ #{λ ∈ σ(Hₙ) : λ < −ε} ≤ r₊`."

For a sign `s ∈ {+1, −1}` and `t` in the range of §7 (`√d ≤ t` and `t < |µ|` for every informative
eigenvalue `µ` of sign `s`), for every `ε > 0`, with probability tending to one the Bethe Hessian
`H(st, Gₙ)` has at most `r_s` eigenvalues (with multiplicity) below `−ε`, where `r₊₁ = r₊`, `r₋₁ = r₋`.

**Formalization Note.** This is a result of the cited paper [12], stated as this paper invokes it:
for `H(t, Gₙ)` in the proof of Proposition 7.2 and, with `r₋`, for `H(−t, Gₙ)` in the proof of
Theorem 2.2 (p.12). Eigenvalues are the roots of the characteristic polynomial. -/
theorem ref12_corollary_3_4 {r : ℕ} (p : SBMParams r) (s : ℝ) (hs : s = 1 ∨ s = -1) (t : ℝ)
    (ht : Real.sqrt p.d ≤ t) (ht' : ∀ μ ∈ informative p, 0 < s * μ → t < |μ|)
    (σs : ∀ n : ℕ, Fin n → Fin r) (hσ : IsExactSeq p σs) (ε : ℝ) (hε : 0 < ε) :
    Whp p σs (fun _ G =>
      Multiset.card ((bh (s * t) G).charpoly.roots.filter (fun ev => ev < -ε)) ≤
        (if s = 1 then rplus p else rminus p)) := by sorry

end BetheKS
