-- Prove2me | Theorems.Thm_BellRegret_Paradoxes_coexistence_insurance_gambling
-- name    : BellRegret.Paradoxes.coexistence_insurance_gambling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:22:37.864396+00:00
-- url     : https://prove2.me/theorems/c5d777aa-4855-4315-b3d5-aad8b531f7c3
-- title:
--   Sec. 2(i), pp. 971–972 — with f decreasingly concave, the same decision maker takes a fair long-odds bet and buys fair insurance
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be **decreasingly concave**, i.e. twice differentiable with strictly increasing second derivative, and let the decision maker evaluate outcomes by the regret utility
--   $$u(x,y)=x+f(x-y),$$
--   where $x$ is her final assets and $y$ the assets the foregone alternative would have given. Let $0<p<\tfrac12$. Then
--
--   1. **(gambling)** offered a bet of $\$p$ on a horse that wins with probability $p$ and pays $\$1$ if it wins (net $\$(1-p)$ or $-\$p$, Table II), she strictly prefers betting to not betting;
--   2. **(insurance)** facing a $\$1$ loss with probability $p$ and an insurance premium of $\$p$ (Table III), she strictly prefers insuring to not insuring.
--
--   Both options in each comparison have equal expected value, so expected-value reasoning is indifferent, and a concave or convex utility of final assets alone predicts opposite attitudes in the two cases. Regret with decreasingly concave $f$ explains why the same person gambles at long odds and buys insurance.
--
--   **Formalization Note** The page takes $v$ approximately linear and computes with $v(x)=x$; the formalization uses $v(x)=x$ exactly. "Decreasingly concave" is not defined in the paper; it is read as $f''$ strictly increasing (p. 972: "$f''(x)>f''(-x)$ … and, therefore, if $f$ is decreasingly concave"; p. 976: "a positive third derivative"). The page also presumes $f$ increasing and concave (p. 976); these are not assumed, which makes the statement stronger. The page's "p close to zero" is not formalized; $p<\tfrac12$ is. Preferences are strict, as in (5) and (6).
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, pp. 971–972 (PDF 12–13), Sec. 2(i) "The Coexistence of Insurance and Gambling", Tables II–III, displays (5)–(6) and the paragraph after Table III

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

namespace BellRegret.Paradoxes

/-- Sec. 2(i), pp. 971–972 (the coexistence of insurance and gambling): if `f` is
decreasingly concave and `0 < p < 1/2`, then with `u(x, y) = x + f(x − y)` the decision maker
strictly prefers the long-odds bet of Table II to not betting, and strictly prefers buying the
fair insurance of Table III to not insuring. -/
theorem coexistence_insurance_gambling (f : ℝ → ℝ) (hf : DecreasinglyConcave f)
    (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 2) :
    Prefers f (prob2 p) (horseBet p) horseNoBet ∧
      Prefers f (prob2 p) (carInsure p) carNoInsure := by sorry

end BellRegret.Paradoxes
