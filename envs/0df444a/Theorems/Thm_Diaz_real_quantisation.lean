-- Prove2me | Theorems.Thm_Diaz_real_quantisation
-- name    : Diaz.real_quantisation
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:05:21.625237+00:00
-- url     : https://prove2.me/theorems/64b9dbba-c6f9-4c59-92c2-b145fc86ca3c
-- title:
--   Quantisation of the real branch: a candidate with real exponential has $|u|^2 > \pi^2$
-- statement:
--   **Source.** This is Carlo Perassi's mathematics: Theorem 3.1 (*Quantisation*) of his companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). Published on his mission with his permission. No novelty is claimed for it here; the argument is elementary.
--
--   **Statement.** Let $u \in \mathbb{C}$ lie on neither axis ($\Re u \neq 0$, $\Im u \neq 0$) and suppose $e^{u}$ is real. Then $\Im u \in \pi\mathbb{Z}$, and consequently
--   $$u\bar u  =  (\Re u)^2 + (\Im u)^2  >  \pi^2 .$$
--
--   **What it says in the mission's terms.** On the Diaz locus the two axis exclusions are supplied by `Diaz.not_on_axes`, so every candidate whose exponential is real satisfies them. The conclusion is that the *real branch* of the locus is quantised: its points are $\ell + i n \pi$ with $n \in \mathbb{Z}\setminus\{0\}$, and their norms are bounded below by $\pi^2$ — they cannot accumulate at $0$.
--
--   **Why the bound is not formal.** It is exactly the place where the mission's Laurent shadow model (`Diaz.model_falsifies`, `Diaz.Exp0_*`) parts company with the actual exponential. There $\ker \mathrm{Exp}_0$ is a divisible line, the shadow locus is stable under $\mathbb{Q}^\times$, and its norms $q^2\rho$ accumulate at $0$; here $\ker \exp \cap \mathcal{L} = 2\pi i \mathbb{Z}$ is a rank-one lattice inside the divisible line $2\pi i\mathbb{Q}$, and both conclusions fail in the model. The real branch is also, unlike the full locus, *not* stable under $\mathbb{Q}^\times$: $qu$ has real exponential only when $qn \in \mathbb{Z}$.
--
--   **Reading the Lean.** `(Complex.exp u).im = 0` is "$e^{u}$ is real"; `Complex.normSq u` is $u \bar u$.
--
--   **Proof.** `Complex.exp_im` gives $(e^{u})_{\mathrm{im}} = e^{\Re u}\sin(\Im u)$, and $e^{\Re u} \neq 0$, so $\sin(\Im u) = 0$ and $\Im u = n\pi$ for some integer $n$. Since $\Im u \neq 0$ we have $n \neq 0$, hence $|\Im u| \geq \pi$ and $(\Im u)^2 \geq \pi^2$; adding $(\Re u)^2 > 0$ gives the strict inequality.

import Mathlib

open ComplexConjugate

theorem Diaz.real_quantisation {u : ℂ} (hexp : (Complex.exp u).im = 0)
    (hre : u.re ≠ 0) (him : u.im ≠ 0) :
    (∃ n : ℤ, u.im = n * Real.pi) ∧ Real.pi ^ 2 < Complex.normSq u := by sorry
