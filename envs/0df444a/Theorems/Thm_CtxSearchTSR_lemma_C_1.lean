-- Prove2me | Theorems.Thm_CtxSearchTSR_lemma_C_1
-- name    : CtxSearchTSR.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:57.151489+00:00
-- url     : https://prove2.me/theorems/5a632df5-e3a0-46d6-ac05-02671d24edbb
-- title:
--   Lemma C.1 — one-dimensional potential decrease (28)–(29)
-- statement:
--   Let $m,z\in\mathbb R$ and $r>0$, and $\varphi(m,r,z)=r+(m-z)^2/r$. Let $\varepsilon$ be uniform on $\{-1,1\}$ and set
--
--   $$P=m+\frac r2\varepsilon,\quad Y=\operatorname{sign}(z-P),\quad m^+=m+\frac{rY}{3-\varepsilon Y},\quad r^+=\frac{3r}{3-\varepsilon Y},$$
--
--   with $\operatorname{sign}(0)=1$. Then
--
--   $$\varphi(m,r,z)-\mathbb E_\varepsilon\bigl[\varphi(m^+,r^+,z)\bigr]\ \ge\ \frac16\,\mathbb E_\varepsilon\bigl[|z-P|\bigr]=\frac16\max\Bigl\{|z-m|,\frac r2\Bigr\}, \tag{28}$$
--
--   and in particular
--
--   $$\mathbb E_\varepsilon\bigl[\varphi(m^+,r^+,z)\bigr]\le\varphi(m,r,z)-\frac r{12}. \tag{29}$$
--
--   This is the one-dimensional engine of the analysis: after projecting onto the current context, each round of Algorithm 2 is this two-price scheme.
--
--   **Formalization Note** $\mathbb E_\varepsilon f=\tfrac12\bigl(f(1)+f(-1)\bigr)$. The three conclusions are the inequality and the equality of (28), and (29).
--
--   Differences from the source:
--   - encoding: 𝔼_ε over ε uniform on {−1, 1} → (f(1) + f(−1))/2; reason: the uniform law on two points
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), App. C.1, Lemma C.1, p.19, (28)–(29)

import Mathlib
import Definitions.Def_CtxSearchTSR_Algorithm2
import Definitions.Def_CtxSearchTSR_Potentials

open Matrix

namespace CtxSearchTSR

/-- **Lemma C.1 (One-dimensional potential decrease).** Cosson et al., *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*, STOC 2027
submission (manuscript sha256 70eeb0d1…), App. C.1, p.19,
(28)–(29).

For m, z ∈ ℝ and r > 0, with φ(m, r, z) = r + (m − z)²/r, ε uniform on {−1, 1},
P = m + (r/2)ε, Y = sign(z − P), m⁺ = m + rY/(3 − εY) and r⁺ = 3r/(3 − εY):

* φ(m, r, z) − 𝔼_ε[φ(m⁺, r⁺, z)] ≥ (1/6) 𝔼_ε[|z − P|]  (28, inequality);
* (1/6) 𝔼_ε[|z − P|] = (1/6) max{|z − m|, r/2}  (28, equality);
* 𝔼_ε[φ(m⁺, r⁺, z)] ≤ φ(m, r, z) − r/12  (29).

**Formalization Note.** 𝔼_ε f = (f(1) + f(−1))/2. sign(0) = 1 (`sgn0`), which matters at the
boundary |z − m| = r/2. -/
theorem lemma_C_1 (m z r : ℝ) (hr : 0 < r) :
    let P : ℝ → ℝ := fun e => m + r / 2 * e
    let Y : ℝ → ℝ := fun e => sgn0 (z - P e)
    let mp : ℝ → ℝ := fun e => m + r * Y e / (3 - e * Y e)
    let rp : ℝ → ℝ := fun e => 3 * r / (3 - e * Y e)
    let E : (ℝ → ℝ) → ℝ := fun f => (f 1 + f (-1)) / 2
    (1 / 6) * E (fun e => |z - P e|) ≤ phi m r z - E (fun e => phi (mp e) (rp e) z) ∧
    (1 / 6) * E (fun e => |z - P e|) = (1 / 6) * max |z - m| (r / 2) ∧
    E (fun e => phi (mp e) (rp e) z) ≤ phi m r z - r / 12 := by sorry

end CtxSearchTSR
